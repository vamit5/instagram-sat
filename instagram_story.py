"""
Skripta koja automatski objavljuje INSTAGRAM STORIES (ne Reels) koristeci
SAMO prioritetne klipove (fajlovi cije ime sadrzi "prioritet") sa Google
Drive foldera, u krug (rotation), nekoliko puta dnevno. Story traje samo
24h na Instagramu -- klip se samo kompresuje/skalira (isti pristup kao za
prioritetne Reels objave, bez teksta i bez tajmera) i objavi kao Story.

Deli isti state.json fajl sa glavnom instagram_post.py skriptom, ali
koristi ODVOJEN kljuc (story_last_index) da ne remeti rotaciju obicnih
Reels objava.

Ne treba ovo pokretati rucno -- GitHub Actions to radi sam, po rasporedu.
"""

import os
import json
import re
import time
import subprocess
import requests
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload

SCOPES = ["https://www.googleapis.com/auth/drive.readonly"]
STATE_FILE = "state.json"
GRAPH_VERSION = "v21.0"
API_BASE = "https://graph.instagram.com"

CLOUDINARY_CLOUD_NAME = "dnbjvccgy"
CLOUDINARY_UPLOAD_PRESET = "instagram_bot"

PRIORITY_PATTERN = re.compile(r"prioritet", re.IGNORECASE)
TIMER_CLIP_PATTERN = re.compile(r"2\s*minute\s*timer", re.IGNORECASE)

MAX_VIDEO_DIMENSION = 1080

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
    creds = service_account.Credentials.from_service_account_info(creds_dict, scopes=SCOPES)
    return build("drive", "v3", credentials=creds)


def list_videos(service, folder_id):
    query = f"'{folder_id}' in parents and mimeType contains 'video/' and trashed=false"

    def call():
        return service.files().list(
            q=query,
            fields="files(id, name, createdTime)",
            orderBy="createdTime",
        ).execute()

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


def get_video_dimensions(local_path):
    def call():
        result = subprocess.run(
            [
                "ffprobe", "-v", "error", "-select_streams", "v:0",
                "-show_entries", "stream=width,height:stream_tags=rotate:stream_side_data=rotation",
                "-of", "json", local_path,
            ],
            capture_output=True, text=True, check=True,
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


def compute_capped_dimensions(width, height, max_dim=MAX_VIDEO_DIMENSION):
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
    width, height = get_video_dimensions(local_in)
    target_w, target_h = compute_capped_dimensions(width, height)
    cmd = [
        "ffmpeg", "-y", "-i", local_in,
        "-vf", f"scale={target_w}:{target_h}",
        "-c:v", "libx264", "-crf", "23", "-preset", "veryfast",
        "-maxrate", "4M", "-bufsize", "8M",
        "-c:a", "aac", "-b:a", "128k",
        local_out,
    ]
    print("Kompresujem story klip:", " ".join(cmd))
    with_retry(subprocess.run, cmd, retries=2, delay=3, check=True)


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
    return {}


def save_state(state):
    with open(STATE_FILE, "w") as f:
        json.dump(state, f, indent=2)


def create_story_container(ig_user_id, access_token, video_url):
    url = f"{API_BASE}/{GRAPH_VERSION}/{ig_user_id}/media"
    payload = {
        "media_type": "STORIES",
        "video_url": video_url,
        "access_token": access_token,
    }

    def call():
        r = requests.post(url, data=payload, timeout=60)
        if not r.ok:
            print("Greska pri kreiranju story medija:", r.text)
        r.raise_for_status()
        return r.json()["id"]

    return with_retry(call)


def wait_for_container(container_id, access_token, timeout=600):
    url = f"{API_BASE}/{GRAPH_VERSION}/{container_id}"
    start = time.time()
    while time.time() - start < timeout:
        try:
            r = requests.get(
                url, params={"fields": "status_code,status", "access_token": access_token}, timeout=30
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
            error_detail = r.json().get("status", "nepoznato")
            raise RuntimeError(f"Instagram je prijavio gresku pri obradi story videa: {error_detail}")
        time.sleep(10)
    raise TimeoutError("Isteklo je vreme cekanja na obradu story videa.")


def publish_container(ig_user_id, access_token, container_id):
    url = f"{API_BASE}/{GRAPH_VERSION}/{ig_user_id}/media_publish"
    payload = {"creation_id": container_id, "access_token": access_token}

    def call():
        r = requests.post(url, data=payload, timeout=60)
        if not r.ok:
            print("Greska pri objavljivanju story-ja:", r.text)
        r.raise_for_status()
        return r.json()

    return with_retry(call)


def is_priority_clip(video):
    return bool(PRIORITY_PATTERN.search(video["name"]))


def is_timer_clip(video):
    return bool(TIMER_CLIP_PATTERN.search(video["name"]))


def main():
    access_token = os.environ["IG_ACCESS_TOKEN"]
    ig_user_id = os.environ["IG_ACCOUNT_ID"]
    folder_id = os.environ["GDRIVE_FOLDER_ID"]

    drive = get_drive_service()
    videos = list_videos(drive, folder_id)

    priority_videos = [v for v in videos if is_priority_clip(v) and not is_timer_clip(v)]

    if not priority_videos:
        print("Nema prioritetnih klipova za Story objavu. Preskacem.")
        return

    state = load_state()
    last_index = state.get("story_last_index", -1)
    next_index = (last_index + 1) % len(priority_videos)
    video = priority_videos[next_index]
    print(f"Story redosled: {next_index + 1}/{len(priority_videos)} -- {video['name']}")

    local_in = "story_original.mp4"
    download_file(drive, video["id"], local_in)

    local_out = "story_kompresovan.mp4"
    compress_video(local_in, local_out)

    video_url = upload_to_cloudinary(local_out)
    print(f"Story video otpremljen na: {video_url}")

    container_id = create_story_container(ig_user_id, access_token, video_url)
    wait_for_container(container_id, access_token)
    result = publish_container(ig_user_id, access_token, container_id)

    print(f"Story uspesno objavljen! Media ID: {result.get('id')}")

    state["story_last_index"] = next_index
    save_state(state)


if __name__ == "__main__":
    main()
