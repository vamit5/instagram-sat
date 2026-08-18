"""
Skripta koja automatski objavljuje sledeci video (reel) sa Google Drive foldera
na Instagram, u krug (rotation). Kratki klipovi (ispod SHORT_CLIP_THRESHOLD
sekundi) se automatski spajaju sa sledecim kratkim klipovima (istim redom
kojim su na Drive-u) dok zbir ne dostigne MIN_COMBINED_DURATION sekundi.
Duzi klipovi ostaju nepromenjeni, objavljuju se pojedinacno. Spojeni klipovi
ZADRZAVAJU svoj originalni zvuk (ako neki klip nema zvuk, dodaje mu se tiha
audio traka iste duzine, da bi spajanje uopste bilo moguce).

Fajl cije ime sadrzi "2 minute timer" (bilo koje pisanje, velika/mala slova
nebitno) se NIKAD ne tretira kao obican rotacioni klip -- izdvaja se iz
liste za objavu i koristi se kao mali countdown tajmer koji se "zalepi"
preko svakog objavljenog reel-a (i normalnih i prioritetnih), ispod zone
gornjeg teksta i ispod Instagram korisnickog imena. Tajmer je EKSPLICITNO
skracen (preko ffmpeg "-t" opcije na ulazu) na TACNU duzinu glavnog videa
PRE spajanja, plus "-shortest" kao dodatna sigurnosna mera -- garantuje da
konacan video NIKAD ne bude duzi od stvarnog reel-a, cak i kad je tajmer
(2 min) duzi od samog klipa.

Trajanje svakog videa se prvo pokusava ocitati iz Google Drive metapodataka
(brzo, bez preuzimanja). Ako Drive to jos nije izracunao (cesto slucaj sa
netom otpremljenim fajlovima), skripta SAMA preuzme taj video i izmeri
trajanje preko ffprobe -- ovo garantuje da kratak video nikad ne prodje kao
"dug" zbog nedostajucih metapodataka.

Pre objave, na video dodaje tekst SA PRAVIM emoji slicicama (preuzetim sa
interneta), jer ffmpeg sam po sebi ne ume da iscrta emotikone u boji. Python
prvo nacrta ceo natpis (tekst + emoji) kao providnu PNG sliku, tacno
izmerenu da stane u zadati broj redova i da bude centrirana, pa se ta slika
"zalepi" preko videa. Ako tekst ne stane ni na najmanjoj velicini slova,
NIKAD se ne brisu reci -- dodaje se jos redova umesto toga.

Gornji i donji tekst se biraju iz "rotirajuce" liste -- isti tekst se NIKAD
ne ponavlja dok se ne iskoriste svi ostali iz liste bar jednom (stanje te
rotacije se cuva u state.json). Ako se lista tekstova promeni u kodu, stari
zapis u state.json se automatski odbacuje i pravi iznova (samo-popravka).

Pre svake objave, skripta proverava TACNU, TRENUTNU iskoriscenost
Instagram publishing kvote za taj nalog -- ako je kvota vec skoro/potpuno
potrosena, tiho preskace umesto da trosi vreme na preuzimanje/obradu
videa koji bi na kraju svejedno pao na "Media Publish Limit Exceeded"
gresci.

Ne treba ovo pokretati rucno -- GitHub Actions to radi sam, po rasporedu.
"""

import os
import io
import json
import re
import time
import random
import subprocess
import requests
from PIL import Image, ImageDraw, ImageFont
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload

SCOPES = ["https://www.googleapis.com/auth/drive.readonly"]
STATE_FILE = "state.json"
GRAPH_VERSION = "v21.0"
API_BASE = "https://graph.instagram.com"

CLOUDINARY_CLOUD_NAME = "dnbjvccgy"
CLOUDINARY_UPLOAD_PRESET = "instagram_bot"

FONT_PATH = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"
TWEMOJI_BASE = "https://cdn.jsdelivr.net/gh/twitter/twemoji@14.0.2/assets/72x72/"

TOP_TEXT_Y_FRACTION = 0.14
BOTTOM_TEXT_Y_FRACTION = 0.80

# Velicina slova za DONJI tekst (ostaje nepromenjeno, kao do sada).
FONT_BASE_SIZE = 78
FONT_MIN_SIZE = 34

# Velicina slova za GORNJI tekst -- namerno manja ("mala slova", po zahtevu).
TOP_FONT_BASE_SIZE = 54
TOP_FONT_MIN_SIZE = 28

BOX_BORDER = 24
BOX_RADIUS = 18
BOX_COLOR = (0, 0, 0, 140)
TEXT_COLOR = (255, 255, 255, 255)
LINE_HEIGHT_FACTOR = 1.35
MAX_TEXT_WIDTH_FRACTION = 0.86

# Kratki klipovi (u sekundama) se spajaju dok zbir ne dostigne ovoliko.
SHORT_CLIP_THRESHOLD = 9.0
MIN_COMBINED_DURATION = 15.0

TOP_TEXTS = [
    "ŽURKA ZA PONETI 😂",
    "ODMOTAJ I NAPRAVI HAOS U DRUŠTVU.",
    "TRENERI, OVO JE VAŠE ZLATO.",
    "ŽURKA U DŽEPU.",
    "PONESI ŽURKU GDE GOD IDEŠ.",
    "ODMOTAJ OVO I ZA MINUT NASTAJE HAOS 😂",
    "TRENERU, OVO VADIŠ KAD HOĆEŠ DA PODIGNEŠ ATMOSFERU.",
    "ODMOTAJ SAT I ZA 30 sek JE 50 LJUDI OKO TEBE 😂",
    "JEDAN SAT, 100 LJUDI OKOLO 😂",
    "ZA TRENERE KOJI VOLE DA NAPRAVE HAOS.",
    "99% LJUDI NE USPE CEO SAT ZA 2 MIN.",
    "PONESI GA NA TRENING I IZAZOVI CELU EKIPU",
    "IMAŠ 2 MINUTA ZA CEO KRUG",
    "VEĆINA PADNE NA BROJU 10",
    "NAJLAKŠI NAČIN DA NAPRAVIŠ TAKMIČENJE",
    "ODMOTAJ SAT I ZA MINUT JE 50 LJUDI OKO TEBE 😂",
    "JEDAN SAT, A 100 LJUDI SE OKUPILO ZA 1 MINUT 😂",
    "VAMIT-5 SAT - ŽURKA ZA PONETI",
]

BOTTOM_TEXTS = [
    "Poruči danas za samo 19€",
    "Danas samo 19€ (Link u BIO)",
    "Još samo danas 19€",
    "Poruči danas - stiže brzo 🕐",
    "Dostava samo po Srbiji",
]

RULE_TEXT = (
    "Pravilo: Imaš 2 minuta vremena da uradiš ceo VAMIT-5 sat, "
    "grudi do dole, ruke se ispružaju maksimalno, nedozvoljeno je ići na kolena."
)

# Fajlovi cije ime sadrzi ovu rec (bilo gde, velika/mala slova nebitno) se
# tretiraju kao "prioritetni" (viralni) klipovi: (1) svaka PRIORITY_BOOST_EVERY-ta
# objava je "bonus" -- preskace se normalan redosled i ubaci se prioritetan
# klip (rotirajuci i medju njima), i (2) na te klipove se NIKAD ne stavlja
# tekst preko videa (samo opis ispod objave ostaje normalan). Timer overlay
# (dole) se PRIMENJUJE i na prioritetne klipove.
PRIORITY_PATTERN = re.compile(r"prioritet", re.IGNORECASE)
PRIORITY_BOOST_EVERY = 3

# Fajl sa ovim imenom (bilo gde u nazivu, velika/mala slova nebitno) se NIKAD
# ne tretira kao obican rotacioni klip -- to je mali countdown tajmer koji
# se "zalepi" preko svakog objavljenog reel-a.
TIMER_CLIP_PATTERN = re.compile(r"2\s*minute\s*timer", re.IGNORECASE)
TIMER_LOCAL_PATH = "timer_clip.mov"
TIMER_WIDTH_FRACTION = 0.32  # sirina tajmera kao % sirine videa
TIMER_MARGIN_FRACTION = 0.04  # razmak od LEVE ivice kadra
TIMER_Y_FRACTION = 0.34  # razmak od GORNJE ivice -- dodatno spusteno nadole

# Koliko puta da se pokusa ponovo (uz pauzu koja se svaki put duplira) pre
# nego sto se stvarno odustane od mreznog poziva -- ovo pokriva velecinu
# povremenih, prolaznih gresaka (Drive, Cloudinary, Instagram API).
RETRY_ATTEMPTS = 5
RETRY_BASE_DELAY = 5


def with_retry(func, *args, retries=RETRY_ATTEMPTS, delay=RETRY_BASE_DELAY, **kwargs):
    attempt = 0
    while True:
        try:
            return func(*args, **kwargs)
        except requests.exceptions.HTTPError as e:
            status = e.response.status_code if e.response is not None else None
            if status is not None and 400 <= status < 500:
                print(f"Trajna greska (HTTP {status}) -- ne pokusavam ponovo: {e}")
                raise
            attempt += 1
            if attempt >= retries:
                print(f"Odustajem posle {attempt} pokusaja: {e}")
                raise
            wait = delay * (2 ** (attempt - 1))
            print(f"Greska ({e}) -- pokusaj {attempt}/{retries}, cekam {wait}s...")
            time.sleep(wait)
        except Exception as e:
            attempt += 1
            if attempt >= retries:
                print(f"Odustajem posle {attempt} pokusaja: {e}")
                raise
            wait = delay * (2 ** (attempt - 1))
            print(f"Greska ({e}) -- pokusaj {attempt}/{retries}, cekam {wait}s...")
            time.sleep(wait)


def get_drive_service():
    creds_json = os.environ["GDRIVE_SERVICE_ACCOUNT_JSON"]
    creds_dict = json.loads(creds_json)
    creds = service_account.Credentials.from_service_account_info(
        creds_dict, scopes=SCOPES
    )
    return build("drive", "v3", credentials=creds)


def list_videos(service, folder_id):
    """Vraca listu video fajlova u folderu, sortiranu po datumu dodavanja,
    zajedno sa trajanjem (ako ga je Google Drive vec izracunao)."""
    query = (
        f"'{folder_id}' in parents and mimeType contains 'video/' and trashed=false"
    )

    def call():
        return (
            service.files()
            .list(
                q=query,
                fields="files(id, name, createdTime, videoMediaMetadata(durationMillis))",
                orderBy="createdTime",
            )
            .execute()
        )

    results = with_retry(call)
    return results.get("files", [])


def download_file(service, file_id, local_path):
    def call():
        request = service.files().get_media(fileId=file_id)
        with open(local_path, "wb") as f:
            downloader = MediaIoBaseDownload(f, request)
            done = False
            while not done:
                status, done = downloader.next_chunk(num_retries=RETRY_ATTEMPTS)
                if status:
                    print(f"Preuzimanje: {int(status.progress() * 100)}%")

    with_retry(call)


def get_duration_via_ffprobe(local_path):
    def call():
        result = subprocess.run(
            [
                "ffprobe", "-v", "error",
                "-show_entries", "format=duration",
                "-of", "json",
                local_path,
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        data = json.loads(result.stdout)
        return float(data["format"]["duration"])

    return with_retry(call, retries=2, delay=2)


def has_audio_stream(local_path):
    def call():
        result = subprocess.run(
            [
                "ffprobe", "-v", "error",
                "-select_streams", "a",
                "-show_entries", "stream=index",
                "-of", "json",
                local_path,
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        data = json.loads(result.stdout)
        return len(data.get("streams", [])) > 0

    return with_retry(call, retries=2, delay=2)


def ensure_durations(drive, videos):
    """Za svaki video kome Drive JOS NIJE izracunao trajanje (cesto kod
    netom otpremljenih fajlova), skripta ga sama preuzme i izmeri stvarno
    trajanje preko ffprobe. Preuzeti fajl se cuva (u video['_probed_path'])
    da se ne bi preuzimao dvaput ako bas taj video bude izabran za objavu
    u ovom pokretanju."""
    for video in videos:
        meta = video.get("videoMediaMetadata", {})
        ms = meta.get("durationMillis")
        if ms is not None:
            video["_duration"] = int(ms) / 1000.0
            continue

        local_path = f"probe_{video['id']}.mp4"
        try:
            download_file(drive, video["id"], local_path)
            video["_duration"] = get_duration_via_ffprobe(local_path)
            video["_probed_path"] = local_path
            print(f"Drive nije imao trajanje za '{video['name']}', izmereno: {video['_duration']:.1f}s")
        except Exception as e:
            print(f"Ne mogu da izmerim trajanje za '{video['name']}': {e} -- tretiram kao dug video.")
            video["_duration"] = None


def build_playlist(videos):
    """Pravi listu 'jedinica za objavu'. Video kraci od SHORT_CLIP_THRESHOLD
    sekundi se sakuplja u zajednicku 'korpu' -- BEZ OBZIRA da li se izmedju
    kratkih klipova nalaze duzi videi (duzi videi se odmah dodaju u listu
    pojedinacno, ali ne prekidaju sakupljanje kratkih klipova u pozadini).
    Cim zbir kratkih klipova dostigne MIN_COMBINED_DURATION sekundi, oni se
    spajaju u jednu objavu. Ovo garantuje da kratak klip NIKAD ne ostane
    usamljen samo zato sto je izmedju dva duga videa na Drive-u."""
    playlist = []
    buffer = []
    buffer_duration = 0.0

    def flush():
        nonlocal buffer, buffer_duration
        if buffer:
            playlist.append(list(buffer))
            buffer = []
            buffer_duration = 0.0

    for video in videos:
        duration = video.get("_duration")
        if duration is None or duration >= SHORT_CLIP_THRESHOLD:
            playlist.append([video])
        else:
            buffer.append(video)
            buffer_duration += duration
            if buffer_duration >= MIN_COMBINED_DURATION:
                flush()
    flush()
    return playlist


def get_video_dimensions(local_path):
    """Vraca STVARNE (prikazane) dimenzije videa, uzimajuci u obzir
    rotacione metapodatke koje telefoni cesto upisuju."""
    def call():
        result = subprocess.run(
            [
                "ffprobe",
                "-v", "error",
                "-select_streams", "v:0",
                "-show_entries", "stream=width,height:stream_tags=rotate:stream_side_data=rotation",
                "-of", "json",
                local_path,
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        data = json.loads(result.stdout)
        stream = data["streams"][0]
        width = stream["width"]
        height = stream["height"]

        rotation = 0
        tags = stream.get("tags", {})
        if "rotate" in tags:
            rotation = int(tags["rotate"])
        for sd in stream.get("side_data_list", []):
            if "rotation" in sd:
                rotation = int(sd["rotation"])

        rotation = rotation % 360
        if rotation in (90, 270):
            return height, width
        return width, height

    return with_retry(call, retries=2, delay=2)


def get_local_path(drive, video, target_path):
    """Ako je video vec preuzet tokom merenja trajanja (ensure_durations),
    samo ga premesti na ciljnu putanju umesto ponovnog preuzimanja."""
    probed_path = video.get("_probed_path")
    if probed_path and os.path.exists(probed_path):
        os.replace(probed_path, target_path)
    else:
        download_file(drive, video["id"], target_path)


def concatenate_clips(local_paths, durations, output_path):
    """Spaja vise kratkih klipova u jedan video, CUVAJUCI zvuk svakog
    klipa. Ako neki klip nema audio traku, dodaje mu se tiha traka iste
    duzine (inace spajanje video+audio streamova ne bi bilo moguce)."""
    target_w, target_h = get_video_dimensions(local_paths[0])
    target_w, target_h = compute_capped_dimensions(target_w, target_h)

    inputs = []
    for path in local_paths:
        inputs += ["-i", path]

    audio_input_map = {}
    lavfi_inputs = []
    next_index = len(local_paths)
    for i, (path, duration) in enumerate(zip(local_paths, durations)):
        if has_audio_stream(path):
            audio_input_map[i] = i
        else:
            lavfi_inputs += [
                "-f", "lavfi", "-t", f"{max(duration, 0.1):.3f}",
                "-i", "anullsrc=r=44100:cl=stereo",
            ]
            audio_input_map[i] = next_index
            next_index += 1
    inputs += lavfi_inputs

    video_parts = []
    audio_parts = []
    concat_refs = ""
    for i, path in enumerate(local_paths):
        video_parts.append(
            f"[{i}:v]scale={target_w}:{target_h}:force_original_aspect_ratio=decrease,"
            f"pad={target_w}:{target_h}:(ow-iw)/2:(oh-ih)/2,setsar=1,fps=30[v{i}]"
        )
        a_idx = audio_input_map[i]
        audio_parts.append(
            f"[{a_idx}:a]aformat=sample_rates=44100:channel_layouts=stereo,"
            f"asetpts=PTS-STARTPTS[a{i}]"
        )
        concat_refs += f"[v{i}][a{i}]"

    filter_complex = (
        ";".join(video_parts) + ";" +
        ";".join(audio_parts) + ";" +
        concat_refs + f"concat=n={len(local_paths)}:v=1:a=1[outv][outa]"
    )

    cmd = ["ffmpeg", "-y"] + inputs + [
        "-filter_complex", filter_complex,
        "-map", "[outv]", "-map", "[outa]",
        "-c:v", "libx264", "-crf", "23", "-preset", "veryfast",
        "-maxrate", "4M", "-bufsize", "8M",
        "-c:a", "aac", "-b:a", "128k",
        output_path,
    ]
    print("Spajam klipove (sa zvukom):", " ".join(cmd))
    with_retry(subprocess.run, cmd, retries=2, delay=3, check=True)


EMOJI_PATTERN = re.compile(
    "["
    "\U0001F300-\U0001FAFF"
    "\U00002600-\U000027BF"
    "\U0001F1E6-\U0001F1FF"
    "\U00002190-\U000021FF"
    "\uFE0F"
    "]+",
    flags=re.UNICODE,
)


def tokenize(text):
    """Deli tekst na 'reci' i 'emoji grupe', cuvajuci redosled, da bi
    moglo da se meri i prelama red po red uzimajuci u obzir oboje."""
    tokens = []
    pos = 0
    for m in EMOJI_PATTERN.finditer(text):
        before = text[pos:m.start()]
        for w in before.split():
            tokens.append({"text": w, "emoji": False})
        tokens.append({"text": m.group(), "emoji": True})
        pos = m.end()
    for w in text[pos:].split():
        tokens.append({"text": w, "emoji": False})
    return tokens


def token_width(token, font, fontsize):
    if token["emoji"]:
        return fontsize * len(token["text"])
    return font.getlength(token["text"])


def line_width(line, font, fontsize, space_w):
    total = 0
    for i, tok in enumerate(line):
        total += token_width(tok, font, fontsize)
        if i < len(line) - 1:
            total += space_w
    return total


def wrap_tokens(tokens, font, fontsize, max_width_px):
    space_w = font.getlength(" ")
    lines = []
    current = []
    current_w = 0
    for tok in tokens:
        w = token_width(tok, font, fontsize)
        added = w if not current else w + space_w
        if current and current_w + added > max_width_px:
            lines.append(current)
            current = [tok]
            current_w = w
        else:
            current.append(tok)
            current_w += added
    if current:
        lines.append(current)
    return lines


def fit_tokens(text, video_width, max_lines, base_size=FONT_BASE_SIZE, min_size=FONT_MIN_SIZE):
    max_width_px = int(video_width * MAX_TEXT_WIDTH_FRACTION) - (2 * BOX_BORDER)
    max_width_px = max(max_width_px, 50)
    tokens = tokenize(text)

    fontsize = base_size
    while fontsize >= min_size:
        font = ImageFont.truetype(FONT_PATH, fontsize)
        lines = wrap_tokens(tokens, font, fontsize, max_width_px)
        space_w = font.getlength(" ")
        fits = all(line_width(l, font, fontsize, space_w) <= max_width_px for l in lines)
        if len(lines) <= max_lines and fits:
            return lines, fontsize
        fontsize -= 2

    # Ako ni na najmanjoj velicini ne stane u trazeni broj redova, NIKAD ne
    # brisemo reci -- vracamo SVE redove (makar bilo vise redova nego sto
    # je trazeno). Bolje veci natpis nego odsecen tekst.
    font = ImageFont.truetype(FONT_PATH, min_size)
    lines = wrap_tokens(tokens, font, min_size, max_width_px)
    return lines, min_size


def get_emoji_image(char, size, cache):
    codepoint = format(ord(char), "x")
    key = (codepoint, size)
    if key in cache:
        return cache[key]
    url = TWEMOJI_BASE + codepoint + ".png"
    img = None
    try:
        def fetch():
            r = requests.get(url, timeout=15)
            r.raise_for_status()
            return r.content

        content = with_retry(fetch, retries=3, delay=3)
        img = Image.open(io.BytesIO(content)).convert("RGBA")
        img = img.resize((size, size), Image.LANCZOS)
    except Exception as e:
        print(f"Ne mogu da preuzmem emoji ({char}) posle vise pokusaja: {e} -- preskacem ga.")
    cache[key] = img
    return img


def render_caption_image(lines, fontsize, emoji_cache):
    font = ImageFont.truetype(FONT_PATH, fontsize)
    space_w = font.getlength(" ")
    line_height = int(fontsize * LINE_HEIGHT_FACTOR)

    widths = [line_width(l, font, fontsize, space_w) for l in lines]
    content_width = int(max(widths)) if widths else 0
    content_height = line_height * len(lines)

    img_w = content_width + 2 * BOX_BORDER
    img_h = content_height + 2 * BOX_BORDER

    img = Image.new("RGBA", (img_w, img_h), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    draw.rounded_rectangle([0, 0, img_w, img_h], radius=BOX_RADIUS, fill=BOX_COLOR)

    y = BOX_BORDER
    for line, lw in zip(lines, widths):
        x = BOX_BORDER + (content_width - lw) / 2
        for tok in line:
            if tok["emoji"]:
                for ch in tok["text"]:
                    em_img = get_emoji_image(ch, fontsize, emoji_cache)
                    if em_img is not None:
                        paste_y = int(y + (line_height - fontsize) / 2)
                        img.paste(em_img, (int(x), paste_y), em_img)
                    x += fontsize
            else:
                draw.text((x, y + (line_height - fontsize) / 2), tok["text"], font=font, fill=TEXT_COLOR)
                x += font.getlength(tok["text"])
            x += space_w
        y += line_height

    return img


MAX_VIDEO_DIMENSION = 1080


def compute_capped_dimensions(width, height, max_dim=MAX_VIDEO_DIMENSION):
    """Smanjuje rezoluciju (cuvajuci proporcije) ako je veca strana preko
    max_dim -- ovo je kljucno za velicinu fajla: sam CRF (kvalitet) ne
    pomaze mnogo ako je izvorni video u 4K ili slicnoj visokoj rezoluciji,
    fajl ostaje ogroman. Vraca dimenzije zaokruzene na paran broj (potrebno
    za video kodek)."""
    if max(width, height) <= max_dim:
        new_w, new_h = width, height
    elif width >= height:
        new_w = max_dim
        new_h = int(height * max_dim / width)
    else:
        new_h = max_dim
        new_w = int(width * max_dim / height)
    new_w -= new_w % 2
    new_h -= new_h % 2
    return max(new_w, 2), max(new_h, 2)


def compress_video(local_in, local_out):
    """Samo kompresuje video (bez ikakvog teksta preko njega) -- koristi
    se za prioritetne klipove. Smanjuje i rezoluciju na max 1080px (veca
    strana) da bi fajl sigurno bio ispod Cloudinary limita."""
    width, height = get_video_dimensions(local_in)
    target_w, target_h = compute_capped_dimensions(width, height)
    cmd = [
        "ffmpeg", "-y",
        "-i", local_in,
        "-vf", f"scale={target_w}:{target_h}",
        "-c:v", "libx264", "-crf", "23", "-preset", "veryfast",
        "-maxrate", "4M", "-bufsize", "8M",
        "-c:a", "aac", "-b:a", "128k",
        local_out,
    ]
    print("Kompresujem prioritetan klip (bez teksta):", " ".join(cmd))
    with_retry(subprocess.run, cmd, retries=2, delay=3, check=True)


def add_text_overlay(local_in, local_out, width, height, top_original, bottom_original):
    target_w, target_h = compute_capped_dimensions(width, height)
    emoji_cache = {}

    top_lines, top_size = fit_tokens(
        top_original, target_w, max_lines=2,
        base_size=TOP_FONT_BASE_SIZE, min_size=TOP_FONT_MIN_SIZE,
    )
    bottom_lines, bottom_size = fit_tokens(bottom_original, target_w, max_lines=1)

    top_img = render_caption_image(top_lines, top_size, emoji_cache)
    bottom_img = render_caption_image(bottom_lines, bottom_size, emoji_cache)

    top_path = "top_overlay.png"
    bottom_path = "bottom_overlay.png"
    top_img.save(top_path)
    bottom_img.save(bottom_path)

    top_y = int(target_h * TOP_TEXT_Y_FRACTION)
    bottom_y = int(target_h * BOTTOM_TEXT_Y_FRACTION)

    filter_complex = (
        f"[0:v]scale={target_w}:{target_h}[base];"
        f"[base][1:v]overlay=(W-w)/2:{top_y}[tmp1];"
        f"[tmp1][2:v]overlay=(W-w)/2:{bottom_y}"
    )

    cmd = [
        "ffmpeg", "-y",
        "-i", local_in,
        "-i", top_path,
        "-i", bottom_path,
        "-filter_complex", filter_complex,
        "-c:v", "libx264", "-crf", "23", "-preset", "veryfast",
        "-maxrate", "4M", "-bufsize", "8M",
        "-c:a", "aac", "-b:a", "128k",
        local_out,
    ]
    print("Pokrecem ffmpeg:", " ".join(cmd))
    with_retry(subprocess.run, cmd, retries=2, delay=3, check=True)


def is_timer_clip(video):
    return bool(TIMER_CLIP_PATTERN.search(video["name"]))


def apply_timer_overlay(local_in, local_out, timer_path):
    """Dodaje mali countdown tajmer preko videa, ispod IG korisnickog
    imena i ispod gornjeg teksta. KLJUCNO: tajmer input se EKSPLICITNO
    skracuje (preko "-t" opcije na ulazu) na TACNU duzinu glavnog videa,
    plus "-shortest" kao dodatna sigurnosna mera -- garantuje da konacan
    video NIKAD ne bude duzi od stvarnog glavnog videa, cak i kad je
    tajmer klip (2 min) duzi od samog reel-a (uobicajen slucaj)."""
    width, height = get_video_dimensions(local_in)
    main_duration = get_duration_via_ffprobe(local_in)

    timer_w = int(width * TIMER_WIDTH_FRACTION)
    timer_w -= timer_w % 2
    x_offset = int(width * TIMER_MARGIN_FRACTION)
    y_offset = int(height * TIMER_Y_FRACTION)

    filter_complex = (
        f"[1:v]scale={timer_w}:-2[timer];"
        f"[0:v][timer]overlay={x_offset}:{y_offset}[outv]"
    )

    cmd = [
        "ffmpeg", "-y",
        "-i", local_in,
        "-t", f"{main_duration:.3f}",
        "-i", timer_path,
        "-filter_complex", filter_complex,
        "-map", "[outv]",
        "-map", "0:a?",
        "-shortest",
        "-c:v", "libx264", "-crf", "23", "-preset", "veryfast",
        "-maxrate", "4M", "-bufsize", "8M",
        "-c:a", "aac", "-b:a", "128k",
        local_out,
    ]
    print("Dodajem tajmer overlay:", " ".join(cmd))
    with_retry(subprocess.run, cmd, retries=2, delay=3, check=True)


def build_caption(top_original, bottom_original):
    return (
        f"{top_original}\n"
        f"{bottom_original}\n\n"
        f"#vamit5sat\n"
        f"Link ka Online Shopu je u opisu profila!\n\n"
        f"{RULE_TEXT}"
    )


def upload_to_cloudinary(local_path):
    url = f"https://api.cloudinary.com/v1_1/{CLOUDINARY_CLOUD_NAME}/video/upload"

    def call():
        with open(local_path, "rb") as f:
            files = {"file": f}
            data = {"upload_preset": CLOUDINARY_UPLOAD_PRESET}
            r = requests.post(url, files=files, data=data, timeout=300)
        if not r.ok:
            print("Greska pri otpremanju na Cloudinary:", r.text)
        r.raise_for_status()
        return r.json()["secure_url"]

    return with_retry(call)


def load_state():
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE) as f:
            return json.load(f)
    return {"last_index": -1}


def save_state(state):
    with open(STATE_FILE, "w") as f:
        json.dump(state, f, indent=2)


def pick_next_text(state, key, options):
    """Bira sledeci tekst iz liste tako da se NIKAD ne ponovi dok se ne
    iskoriste svi ostali iz liste bar jednom (tzv. 'shuffled bag'
    pristup). Kad se lista potrosi, pravi se nova, nasumicno promesana
    runda -- vodi se racuna da se ne ponovi tekst sa kraja prethodne
    runde odmah na pocetku nove.

    Ako se lista tekstova (TOP_TEXTS/BOTTOM_TEXTS) promeni u kodu, stari
    sacuvani indeksi u state.json vise ne bi odgovarali tacnim tekstovima
    -- zato se queue AUTOMATSKI odbacuje i pravi iznova ako sadrzi bilo
    koji indeks van opsega trenutne liste."""
    queue_key = f"{key}_queue"
    last_key = f"{key}_last"

    queue = state.get(queue_key, [])
    if not queue or any(i >= len(options) for i in queue):
        queue = list(range(len(options)))
        random.shuffle(queue)
        last = state.get(last_key)
        if len(queue) > 1 and queue[0] == last:
            queue[0], queue[1] = queue[1], queue[0]

    idx = queue.pop(0)
    state[queue_key] = queue
    state[last_key] = idx
    return options[idx]


def create_media_container(ig_user_id, access_token, video_url, caption=""):
    url = f"{API_BASE}/{GRAPH_VERSION}/{ig_user_id}/media"
    payload = {
        "media_type": "REELS",
        "video_url": video_url,
        "caption": caption,
        "access_token": access_token,
    }

    def call():
        r = requests.post(url, data=payload, timeout=60)
        if not r.ok:
            print("Greska pri kreiranju medija:", r.text)
        r.raise_for_status()
        return r.json()["id"]

    return with_retry(call)


def wait_for_container(container_id, access_token, timeout=600):
    url = f"{API_BASE}/{GRAPH_VERSION}/{container_id}"
    start = time.time()
    while time.time() - start < timeout:
        try:
            r = requests.get(
                url, params={"fields": "status_code", "access_token": access_token}, timeout=30
            )
            r.raise_for_status()
            status = r.json().get("status_code")
        except Exception as e:
            print(f"Privremena greska pri proveri statusa ({e}), pokusavam ponovo...")
            time.sleep(10)
            continue
        print(f"Status obrade: {status}")
        if status == "FINISHED":
            return True
        if status == "ERROR":
            raise RuntimeError("Instagram je prijavio gresku pri obradi videa.")
        time.sleep(10)
    raise TimeoutError("Isteklo je vreme cekanja na obradu videa.")


def publish_container(ig_user_id, access_token, container_id):
    url = f"{API_BASE}/{GRAPH_VERSION}/{ig_user_id}/media_publish"
    payload = {"creation_id": container_id, "access_token": access_token}

    def call():
        r = requests.post(url, data=payload, timeout=60)
        if not r.ok:
            print("Greska pri objavljivanju:", r.text)
        r.raise_for_status()
        return r.json()

    return with_retry(call)


def is_priority_unit(unit):
    return any(PRIORITY_PATTERN.search(video["name"]) for video in unit)


ALLOWED_UTC_HOUR_WINDOWS = [(4, 9), (16, 21)]


def is_within_allowed_window():
    from datetime import datetime, timezone
    hour = datetime.now(timezone.utc).hour
    return any(start <= hour <= end for start, end in ALLOWED_UTC_HOUR_WINDOWS)


QUOTA_SAFETY_MARGIN = 1  # ostavi bar toliko slobodnih mesta kao sigurnosnu marginu


def check_publishing_quota(ig_user_id, access_token):
    """Proverava tacnu, TRENUTNU iskoriscenost Instagram publishing kvote
    za ovaj konkretan nalog (Meta postavlja limit koji moze da varira po
    nalogu, ne uvek isti fiksan broj). Ako provera ne uspe iz bilo kog
    razloga, ne blokira pokretanje -- samo se nastavlja normalno."""
    url = f"{API_BASE}/{GRAPH_VERSION}/{ig_user_id}/content_publishing_limit"
    params = {"fields": "config,quota_usage", "access_token": access_token}

    def call():
        r = requests.get(url, params=params, timeout=30)
        r.raise_for_status()
        return r.json()

    data = with_retry(call)
    entry = data["data"][0]
    usage = entry["quota_usage"]
    total = entry["config"]["quota_total"]
    return usage, total


def main():
    if not is_within_allowed_window():
        print("Van dozvoljenog vremenskog prozora za objavljivanje -- preskacem ovo pokretanje.")
        return

    access_token = os.environ["IG_ACCESS_TOKEN"]
    ig_user_id = os.environ["IG_ACCOUNT_ID"]
    folder_id = os.environ["GDRIVE_FOLDER_ID"]

    try:
        usage, total = check_publishing_quota(ig_user_id, access_token)
        print(f"Instagram publishing kvota: {usage}/{total} iskorisceno u poslednjih 24h.")
        if usage >= total - QUOTA_SAFETY_MARGIN:
            print("Kvota je skoro/potpuno potrosena -- preskacem ovo pokretanje da ne bih trosio resurse uzalud.")
            return
    except Exception as e:
        print(f"Ne mogu da proverim kvotu ({e}) -- nastavljam normalno, pokusacu da objavim.")

    drive = get_drive_service()
    videos = list_videos(drive, folder_id)

    if not videos:
        print("Nema video fajlova u Google Drive folderu. Preskacem.")
        return

    # Izdvoj tajmer klip iz liste PRE bilo cega drugog -- nikad ne sme da
    # udje u obicnu rotaciju.
    timer_video = next((v for v in videos if is_timer_clip(v)), None)
    videos = [v for v in videos if not is_timer_clip(v)]

    if not videos:
        print("Nema video fajlova (posle izdvajanja tajmer klipa) u folderu. Preskacem.")
        return

    timer_local_path = None
    if timer_video:
        try:
            download_file(drive, timer_video["id"], TIMER_LOCAL_PATH)
            timer_local_path = TIMER_LOCAL_PATH
            print(f"Tajmer klip preuzet: {timer_video['name']}")
        except Exception as e:
            print(f"Ne mogu da preuzmem tajmer klip: {e} -- nastavljam bez tajmera.")
    else:
        print("Tajmer klip ('2 Minute Timer') nije pronadjen u folderu -- nastavljam bez tajmera.")

    ensure_durations(drive, videos)
    playlist = build_playlist(videos)
    priority_units = [u for u in playlist if is_priority_unit(u)]

    state = load_state()
    run_counter = state.get("run_counter", 0) + 1
    state["run_counter"] = run_counter

    advance_main_index = True

    if priority_units and run_counter % PRIORITY_BOOST_EVERY == 0:
        p_idx = (state.get("priority_index", -1) + 1) % len(priority_units)
        state["priority_index"] = p_idx
        unit = priority_units[p_idx]
        advance_main_index = False
        print(f"BONUS prioritetna objava ({p_idx + 1}/{len(priority_units)}): {[v['name'] for v in unit]}")
    else:
        next_index = (state["last_index"] + 1) % len(playlist)
        unit = playlist[next_index]
        print(f"Redosled: {next_index + 1}/{len(playlist)} -- fajlova u ovoj objavi: {len(unit)}")

    top_original = pick_next_text(state, "top", TOP_TEXTS)
    bottom_original = pick_next_text(state, "bottom", BOTTOM_TEXTS)
    print(f"DEBUG - Gornji tekst: {top_original!r}")
    print(f"DEBUG - Donji tekst: {bottom_original!r}")
    print(f"DEBUG - Duzina TOP_TEXTS liste u ovom kodu: {len(TOP_TEXTS)}")

    priority = is_priority_unit(unit)
    if priority:
        print("Ovo je prioritetan klip -- BEZ teksta na videu (samo opis ispod objave).")

    if len(unit) == 1:
        local_in = "original.mp4"
        get_local_path(drive, unit[0], local_in)
    else:
        clip_paths = []
        durations = []
        for i, video in enumerate(unit):
            path = f"clip_{i}.mp4"
            get_local_path(drive, video, path)
            clip_paths.append(path)
            durations.append(video.get("_duration") or 1.0)
        local_in = "combined.mp4"
        concatenate_clips(clip_paths, durations, local_in)
        print(f"Spojeno {len(unit)} kratkih klipova u jedan video: {[v['name'] for v in unit]}")

    if priority:
        local_out = "kompresovan.mp4"
        compress_video(local_in, local_out)
        video_to_upload = local_out
    else:
        local_out = "sa_tekstom.mp4"
        width, height = get_video_dimensions(local_in)
        print(f"Dimenzije videa (posle rotacije): {width}x{height}")
        add_text_overlay(local_in, local_out, width, height, top_original, bottom_original)
        video_to_upload = local_out

    if timer_local_path:
        local_with_timer = "sa_tajmerom.mp4"
        apply_timer_overlay(video_to_upload, local_with_timer, timer_local_path)
        video_to_upload = local_with_timer

    video_url = upload_to_cloudinary(video_to_upload)
    print(f"Video otpremljen na: {video_url}")

    caption = build_caption(top_original, bottom_original)

    container_id = create_media_container(ig_user_id, access_token, video_url, caption)
    wait_for_container(container_id, access_token)
    result = publish_container(ig_user_id, access_token, container_id)

    print(f"Uspesno objavljeno! Media ID: {result.get('id')}")

    if advance_main_index:
        state["last_index"] = next_index
    save_state(state)


if __name__ == "__main__":
    main()
