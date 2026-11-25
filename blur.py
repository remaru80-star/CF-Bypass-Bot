"""Blur only the small sensitive areas of an image (NudeNet detector) - used for the post channel thumbnail."""
import threading

from PIL import Image, ImageDraw, ImageFilter

import config

_lock = threading.Lock()
_det = None


def _detector():
    global _det
    if _det is None:
        from nudenet import NudeDetector  # loaded on first use; the model ships inside the package
        _det = NudeDetector()
    return _det


def blur_image(src, dst):
    """Writes a JPEG to dst with each detected area pixelated + softened. Returns how many areas were blurred."""
    with _lock:
        found = _detector().detect(src)
    im = Image.open(src).convert("RGB")
    W, H = im.size
    n = 0
    for d in found:
        if d["class"] not in config.BLUR_LABELS or d["score"] < config.BLUR_CONF:
            continue
        x, y, w, h = d["box"]
        px, py = w * config.BLUR_PAD, h * config.BLUR_PAD
        x0, y0, x1, y1 = max(0, int(x - px)), max(0, int(y - py)), min(W, int(x + w + px)), min(H, int(y + h + py))
        if x1 - x0 < 4 or y1 - y0 < 4:
            continue
        region = im.crop((x0, y0, x1, y1))
        rw, rh = region.size
        small = region.resize((max(2, rw // 10), max(2, rh // 10)), Image.BILINEAR)   # mosaic cells, not reversible
        soft = small.resize((rw, rh), Image.NEAREST).filter(ImageFilter.GaussianBlur(max(2, min(rw, rh) // 12)))
        mask = Image.new("L", (rw, rh), 0)
        ImageDraw.Draw(mask).ellipse((0, 0, rw - 1, rh - 1), fill=255)                # small oval, soft edge
        mask = mask.filter(ImageFilter.GaussianBlur(max(2, min(rw, rh) // 10)))
        im.paste(soft, (x0, y0), mask)
        n += 1
    im.save(dst, "JPEG", quality=92)
    return n