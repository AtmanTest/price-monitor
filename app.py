"""
E-commerce Price Monitor SaaS
Flask app on port 5056
Tracks product prices across stores, sends alerts on drops.
"""
import os
import re
import json
import time
import hashlib
import sqlite3
import threading
from datetime import datetime, timedelta
from functools import wraps
from urllib.parse import urlparse

from flask import (
    Flask, render_template, request, redirect, url_for,
    jsonify, session, g
)
import requests
from bs4 import BeautifulSoup

# ── App Setup ──────────────────────────────────────────────
app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "price-monitor-secret-change-me")
DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "price_monitor.db")

# ── DB Helpers ─────────────────────────────────────────────
def get_db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH, detect_types=sqlite3.PARSE_DECLTYPES)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA journal_mode=WAL")
        g.db.execute("PRAGMA foreign_keys=ON")
    return g.db

@app.teardown_appcontext
def close_db(exception):
    db = g.pop("db", None)
    if db:
        db.close()

def init_db():
    db = sqlite3.connect(DB_PATH)
    db.execute("PRAGMA journal_mode=WAL")
    db.execute("PRAGMA foreign_keys=ON")
    db.executescript("""
        CREATE TABLE IF NOT EXISTS products (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            url TEXT NOT NULL UNIQUE,
            name TEXT NOT NULL,
            store TEXT NOT NULL,
            image_url TEXT DEFAULT '',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            last_checked TIMESTAMP,
            active INTEGER DEFAULT 1
        );

        CREATE TABLE IF NOT EXISTS prices (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            product_id INTEGER NOT NULL,
            price REAL NOT NULL,
            currency TEXT DEFAULT 'EUR',
            scraped_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (product_id) REFERENCES products(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS alerts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            product_id INTEGER NOT NULL,
            alert_type TEXT DEFAULT 'price_drop',
            threshold REAL NOT NULL,
            enabled INTEGER DEFAULT 1,
            triggered_at TIMESTAMP,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (product_id) REFERENCES products(id) ON DELETE CASCADE
        );

        CREATE INDEX IF NOT EXISTS idx_prices_product ON prices(product_id);
        CREATE INDEX IF NOT EXISTS idx_prices_scraped ON prices(scraped_at);
        CREATE INDEX IF NOT EXISTS idx_alerts_product ON alerts(product_id);
    """)
    db.commit()
    db.close()

# ── Scraper Engine ─────────────────────────────────────────
USER_AGENTS = [
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/129.0.0.0 Safari/537.36",
]

PRICE_SELECTORS = [
    # Common CSS-like patterns (we use regex on the text soup)
    r'data-price\s*=\s*["\']([\d.,]+)["\']',
    r'itemprop\s*=\s*["\']price["\'][^>]*content\s*=\s*["\']([\d.,]+)["\']',
    # Amazon-style
    r'"priceAmount"[^>]*>[\s$€£]*([\d.,]+)',
    r'<span[^>]*class="a-price-whole"[^>]*>([\d.,]+)',
    r'<span[^>]*class="a-offscreen"[^>]*>[\s$€£]*([\d.,]+)',
    # General price classes
    r'class\s*=\s*["\'][^"\']*price[^"\']*["\'][^>]*>[\s$€£]*([\d.,]+)',
    r'class\s*=\s*["\'][^"\']*product-price[^"\']*["\'][^>]*>[\s$€£]*([\d.,]+)',
    r'class\s*=\s*["\'][^"\']*sales-price[^"\']*["\'][^>]*>[\s$€£]*([\d.,]+)',
    r'class\s*=\s*["\'][^"\']*current-price[^"\']*["\'][^>]*>[\s$€£]*([\d.,]+)',
    r'class\s*=\s*["\'][^"\']*offer-price[^"\']*["\'][^>]*>[\s$€£]*([\d.,]+)',
    # Meta tags
    r'<meta[^>]*property="product:price:amount"[^>]*content="([\d.,]+)"',
    r'<meta[^>]*name="twitter:data1"[^>]*content="[\s$€£]*([\d.,]+)"',
    # JSON-LD
    r'"price"\s*:\s*"([\d.,]+)"',
    r'"price"\s*:\s*([\d.]+)',
    # Fnac
    r'data-fprice\s*=\s*["\']([\d.,]+)["\']',
    # Darty
    r'data-price-value\s*=\s*["\']([\d.,]+)["\']',
]

CURRENCY_SYMBOLS = {"$": "USD", "€": "EUR", "£": "GBP", "¥": "JPY"}

def detect_store(url):
    domain = urlparse(url).netloc.lower()
    if "amazon" in domain:
        return "Amazon"
    elif "fnac" in domain:
        return "Fnac"
    elif "darty" in domain:
        return "Darty"
    elif "ebay" in domain:
        return "eBay"
    elif "aliexpress" in domain:
        return "AliExpress"
    elif "cdiscount" in domain:
        return "Cdiscount"
    elif "boulanger" in domain:
        return "Boulanger"
    elif "ldlc" in domain:
        return "LDLC"
    else:
        return domain.split(".")[-2].capitalize() if "." in domain else "Unknown"

def detect_currency(text, url):
    domain = urlparse(url).netloc.lower()
    if "€" in text:
        return "EUR"
    if "$" in text:
        if ".fr" in domain or ".de" in domain or ".es" in domain or ".it" in domain:
            return "EUR"
        if ".co.uk" in domain:
            return "GBP"
        return "USD"
    if "£" in text:
        return "GBP"
    if ".fr" in domain or ".de" in domain or ".es" in domain or ".it" in domain:
        return "EUR"
    if ".co.uk" in domain:
        return "GBP"
    return "EUR"

def parse_price(price_str):
    """Parse a price string like '1,299.99' or '1.299,99' to float."""
    if not price_str:
        return None
    price_str = price_str.strip()
    # Detect format: if comma is followed by exactly 2 digits, it's decimal
    if "," in price_str and "." in price_str:
        # Both present: check which is decimal
        if price_str.rfind(",") > price_str.rfind("."):
            # 1.299,99 format
            price_str = price_str.replace(".", "").replace(",", ".")
        else:
            # 1,299.99 format
            price_str = price_str.replace(",", "")
    elif "," in price_str:
        # Only comma: if 2 digits after last comma, it's decimal
        if len(price_str.split(",")[-1]) == 2 and len(price_str.split(",")) > 1:
            price_str = price_str.replace(",", ".")
        else:
            price_str = price_str.replace(",", "")
    try:
        return round(float(re.sub(r"[^\d.]", "", price_str)), 2)
    except (ValueError, TypeError):
        return None

def scrape_price(url):
    """Scrape price from a product URL. Returns (price, currency, product_name) or (None, None, None)."""
    headers = {
        "User-Agent": USER_AGENTS[hash(url) % len(USER_AGENTS)],
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Accept-Language": "fr-FR,fr;q=0.9,en-US;q=0.8,en;q=0.7",
        "Accept-Encoding": "gzip, deflate",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
    }

    try:
        resp = requests.get(url, headers=headers, timeout=15, allow_redirects=True)
        resp.raise_for_status()
    except Exception as e:
        print(f"[scraper] Request failed for {url}: {e}")
        return None, None, None

    html = resp.text

    # Try to find price using regex selectors
    price = None
    currency = detect_currency(html[:5000], url)

    for pattern in PRICE_SELECTORS:
        match = re.search(pattern, html, re.IGNORECASE)
        if match:
            raw = match.group(1)
            price = parse_price(raw)
            if price and 0.01 < price < 1_000_000:
                currency = detect_currency(match.group(0), url)
                break
            else:
                price = None

    # Fallback: BeautifulSoup for structured extraction
    if price is None:
        try:
            soup = BeautifulSoup(html, "html.parser")
            # Try common price elements
            for selector in [
                {"itemprop": "price"},
                {"class": re.compile(r".*price.*", re.I)},
                {"data-price": True},
                {"class": "a-price-whole"},
                {"class": "a-offscreen"},
                {"id": "priceblock_ourprice"},
                {"id": "priceblock_dealprice"},
                {"id": "price_inside_buybox"},
                {"class": "priceToPay"},
            ]:
                if "itemprop" in selector:
                    el = soup.find(attrs=selector)
                    if el and el.get("content"):
                        price = parse_price(el["content"])
                elif "id" in selector:
                    el = soup.find(id=selector["id"])
                    if el:
                        price = parse_price(el.get_text(strip=True))
                elif "data-price" in selector:
                    el = soup.find(attrs={"data-price": True})
                    if el:
                        price = parse_price(el["data-price"])
                else:
                    el = soup.find(attrs=selector)
                    if el:
                        price = parse_price(el.get_text(strip=True))
                if price:
                    break
        except Exception as e:
            print(f"[scraper] BS4 parse failed for {url}: {e}")

    # Extract product name
    name = None
    try:
        soup = BeautifulSoup(html, "html.parser")
        # Try title tag
        title_tag = soup.find("title")
        if title_tag:
            title = title_tag.get_text(strip=True)
            # Clean up title
            title = re.sub(r"\s*[-|]\s*(Amazon|Fnac|Darty|eBay|Cdiscount|AliExpress|Boulanger|LDLC).*$", "", title, flags=re.I)
            title = re.sub(r"\s*:\s*(Amazon|Fnac|Darty).*$", "", title, flags=re.I)
            if len(title) > 10:
                name = title[:200]

        if not name:
            for selector in [
                {"id": "productTitle"},
                {"class": "fnac-title"},
                {"class": "product-title"},
                {"itemprop": "name"},
                {"class": "h1"},
                "h1",
            ]:
                if isinstance(selector, str):
                    el = soup.find(selector)
                else:
                    el = soup.find(attrs=selector)
                if el:
                    name = el.get_text(strip=True)[:200]
                    break
    except:
        pass

    if not name:
        name = urlparse(url).path.split("/")[-1].replace("-", " ")[:200] or "Unknown Product"

    return price, currency, name

# ── Background Checker ─────────────────────────────────────
def check_all_products():
    """Check prices for all active products."""
    db = sqlite3.connect(DB_PATH)
    db.row_factory = sqlite3.Row
    products = db.execute("SELECT * FROM products WHERE active = 1").fetchall()
    db.close()

    results = []
    for product in products:
        print(f"[checker] Checking {product['name'][:60]}...")
        price, currency, _ = scrape_price(product["url"])
        db = sqlite3.connect(DB_PATH)
        if price:
            db.execute(
                "INSERT INTO prices (product_id, price, currency) VALUES (?, ?, ?)",
                (product["id"], price, currency),
            )
            db.execute(
                "UPDATE products SET last_checked = CURRENT_TIMESTAMP WHERE id = ?",
                (product["id"],),
            )

            # Check alerts
            alerts = db.execute(
                "SELECT * FROM alerts WHERE product_id = ? AND enabled = 1 AND triggered_at IS NULL",
                (product["id"],),
            ).fetchall()

            for alert in alerts:
                if alert["alert_type"] == "price_drop" and price <= alert["threshold"]:
                    db.execute(
                        "UPDATE alerts SET triggered_at = CURRENT_TIMESTAMP WHERE id = ?",
                        (alert["id"],),
                    )
                    print(f"[ALERT] Product {product['name']} dropped to {price} (threshold: {alert['threshold']})")

            results.append({"product": product["name"], "price": price, "currency": currency})
        else:
            print(f"[checker] Failed to scrape {product['url']}")
            results.append({"product": product["name"], "price": None, "currency": None})
        db.commit()
        db.close()
        time.sleep(2)  # Be polite between requests

    return results

# ── Routes ─────────────────────────────────────────────────
@app.route("/")
def landing():
    """Landing page for the SaaS."""
    db = get_db()
    product_count = db.execute("SELECT COUNT(*) as c FROM products").fetchone()["c"]
    price_count = db.execute("SELECT COUNT(*) as c FROM prices").fetchone()["c"]
    alert_count = db.execute("SELECT COUNT(*) as c FROM alerts WHERE enabled = 1 AND triggered_at IS NULL").fetchone()["c"]
    return render_template("landing.html", product_count=product_count, price_count=price_count, alert_count=alert_count)

@app.route("/dashboard")
def dashboard():
    """Main dashboard showing tracked products."""
    db = get_db()
    products = db.execute("""
        SELECT p.*, 
               (SELECT price FROM prices WHERE product_id = p.id ORDER BY scraped_at DESC LIMIT 1) as current_price,
               (SELECT currency FROM prices WHERE product_id = p.id ORDER BY scraped_at DESC LIMIT 1) as current_currency,
               (SELECT price FROM prices WHERE product_id = p.id ORDER BY scraped_at ASC LIMIT 1) as first_price,
               (SELECT scraped_at FROM prices WHERE product_id = p.id ORDER BY scraped_at DESC LIMIT 1) as last_price_date
        FROM products p
        ORDER BY p.last_checked DESC
    """).fetchall()

    # Build enriched product list with trend
    enriched = []
    for p in products:
        pid = p["id"]
        # Get last 2 prices for trend
        last_two = db.execute(
            "SELECT price FROM prices WHERE product_id = ? ORDER BY scraped_at DESC LIMIT 2",
            (pid,),
        ).fetchall()
        trend = "neutral"
        if len(last_two) == 2:
            if last_two[0]["price"] < last_two[1]["price"]:
                trend = "down"
            elif last_two[0]["price"] > last_two[1]["price"]:
                trend = "up"

        # Check active alerts
        active_alerts = db.execute(
            "SELECT * FROM alerts WHERE product_id = ? AND enabled = 1 AND triggered_at IS NULL",
            (pid,),
        ).fetchall()

        enriched.append({
            "id": pid,
            "name": p["name"],
            "url": p["url"],
            "store": p["store"],
            "image_url": p["image_url"],
            "current_price": p["current_price"],
            "current_currency": p["current_currency"],
            "first_price": p["first_price"],
            "trend": trend,
            "active_alerts": len(active_alerts),
            "last_price_date": p["last_price_date"],
            "last_checked": p["last_checked"],
        })

    return render_template("dashboard.html", products=enriched)

@app.route("/product/<int:product_id>")
def product_detail(product_id):
    """Product detail with price history."""
    db = get_db()
    product = db.execute("SELECT * FROM products WHERE id = ?", (product_id,)).fetchone()
    if not product:
        return redirect(url_for("dashboard"))

    prices = db.execute(
        "SELECT * FROM prices WHERE product_id = ? ORDER BY scraped_at ASC",
        (product_id,),
    ).fetchall()

    alerts = db.execute(
        "SELECT * FROM alerts WHERE product_id = ? ORDER BY created_at DESC",
        (product_id,),
    ).fetchall()

    # Price history data for chart
    chart_data = [{
        "date": p["scraped_at"],
        "price": p["price"],
        "currency": p["currency"],
    } for p in prices]

    # Compute stats
    price_values = [p["price"] for p in prices]
    stats = {}
    if price_values:
        stats["min"] = min(price_values)
        stats["max"] = max(price_values)
        stats["avg"] = round(sum(price_values) / len(price_values), 2)
        stats["current"] = price_values[-1] if price_values else None
        stats["count"] = len(price_values)
        if len(price_values) >= 2:
            stats["change"] = round(price_values[-1] - price_values[0], 2)
            stats["change_pct"] = round((price_values[-1] - price_values[0]) / price_values[0] * 100, 2)

    return render_template(
        "product.html",
        product=product,
        chart_data=json.dumps(chart_data),
        stats=stats,
        alerts=alerts,
    )

@app.route("/add", methods=["GET", "POST"])
def add_product():
    """Add a new product to track."""
    if request.method == "POST":
        url = request.form.get("url", "").strip()
        if not url:
            return render_template("add.html", error="URL is required")

        # Check if already exists
        db = get_db()
        existing = db.execute("SELECT id FROM products WHERE url = ?", (url,)).fetchone()
        if existing:
            return render_template("add.html", error="This product is already being tracked")

        # Scrape initial data
        price, currency, name = scrape_price(url)
        store = detect_store(url)

        if not name:
            name = request.form.get("name", store + " Product")

        db.execute(
            "INSERT INTO products (url, name, store) VALUES (?, ?, ?)",
            (url, name, store),
        )
        product_id = db.execute("SELECT last_insert_rowid()").fetchone()[0]

        if price:
            db.execute(
                "INSERT INTO prices (product_id, price, currency) VALUES (?, ?, ?)",
                (product_id, price, currency),
            )
            db.execute(
                "UPDATE products SET last_checked = CURRENT_TIMESTAMP WHERE id = ?",
                (product_id,),
            )

        db.commit()
        return redirect(url_for("dashboard"))

    return render_template("add.html", error=None)

@app.route("/delete/<int:product_id>", methods=["POST"])
def delete_product(product_id):
    """Delete a product and its data."""
    db = get_db()
    db.execute("DELETE FROM products WHERE id = ?", (product_id,))
    db.commit()
    return redirect(url_for("dashboard"))

@app.route("/alert/<int:product_id>", methods=["POST"])
def set_alert(product_id):
    """Set a price alert."""
    threshold = float(request.form.get("threshold", 0))
    alert_type = request.form.get("alert_type", "price_drop")

    if threshold <= 0:
        return redirect(url_for("product_detail", product_id=product_id))

    db = get_db()
    db.execute(
        "INSERT INTO alerts (product_id, alert_type, threshold) VALUES (?, ?, ?)",
        (product_id, alert_type, threshold),
    )
    db.commit()
    return redirect(url_for("product_detail", product_id=product_id))

@app.route("/alert/delete/<int:alert_id>", methods=["POST"])
def delete_alert(alert_id):
    """Delete an alert."""
    db = get_db()
    alert = db.execute("SELECT product_id FROM alerts WHERE id = ?", (alert_id,)).fetchone()
    if alert:
        db.execute("DELETE FROM alerts WHERE id = ?", (alert_id,))
        db.commit()
        return redirect(url_for("product_detail", product_id=alert["product_id"]))
    return redirect(url_for("dashboard"))

@app.route("/check-now", methods=["POST"])
def check_now():
    """Manual trigger: check all products."""
    results = check_all_products()
    return redirect(url_for("dashboard"))

@app.route("/check/<int:product_id>", methods=["POST"])
def check_single(product_id):
    """Check a single product."""
    db = get_db()
    product = db.execute("SELECT * FROM products WHERE id = ?", (product_id,)).fetchone()
    if not product:
        return redirect(url_for("dashboard"))

    price, currency, _ = scrape_price(product["url"])
    if price:
        db.execute(
            "INSERT INTO prices (product_id, price, currency) VALUES (?, ?, ?)",
            (product_id, price, currency),
        )
        db.execute(
            "UPDATE products SET last_checked = CURRENT_TIMESTAMP WHERE id = ?",
            (product_id,),
        )

        # Check alerts
        alerts = db.execute(
            "SELECT * FROM alerts WHERE product_id = ? AND enabled = 1 AND triggered_at IS NULL",
            (product_id,),
        ).fetchall()
        for alert in alerts:
            if alert["alert_type"] == "price_drop" and price <= alert["threshold"]:
                db.execute(
                    "UPDATE alerts SET triggered_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (alert["id"],),
                )

        db.commit()
    db.close()
    return redirect(url_for("product_detail", product_id=product_id))

@app.route("/api/prices/<int:product_id>")
def api_prices(product_id):
    """API endpoint for price history."""
    db = get_db()
    prices = db.execute(
        "SELECT price, currency, scraped_at FROM prices WHERE product_id = ? ORDER BY scraped_at ASC",
        (product_id,),
    ).fetchall()
    return jsonify([{
        "price": p["price"],
        "currency": p["currency"],
        "date": p["scraped_at"],
    } for p in prices])

@app.route("/api/stats")
def api_stats():
    """API endpoint for stats."""
    db = get_db()
    stats = {
        "products": db.execute("SELECT COUNT(*) as c FROM products").fetchone()["c"],
        "prices": db.execute("SELECT COUNT(*) as c FROM prices").fetchone()["c"],
        "active_alerts": db.execute("SELECT COUNT(*) as c FROM alerts WHERE enabled = 1 AND triggered_at IS NULL").fetchone()["c"],
        "triggered_alerts": db.execute("SELECT COUNT(*) as c FROM alerts WHERE triggered_at IS NOT NULL").fetchone()["c"],
    }
    return jsonify(stats)

# ── Cron Checker ───────────────────────────────────────────
def cron_checker_loop():
    """Background thread that checks prices every 6 hours."""
    while True:
        print("\n[cron] Starting scheduled price check...")
        try:
            results = check_all_products()
            print(f"[cron] Checked {len(results)} products")
            for r in results:
                if r["price"]:
                    print(f"  {r['product'][:50]}: {r['price']} {r['currency']}")
                else:
                    print(f"  {r['product'][:50]}: FAILED")
        except Exception as e:
            print(f"[cron] Error in check cycle: {e}")
        print(f"[cron] Next check in 6 hours ({datetime.now() + timedelta(hours=6)})\n")
        time.sleep(6 * 3600)  # 6 hours

# ── Main ───────────────────────────────────────────────────
if __name__ == "__main__":
    init_db()
    # Start background cron checker
    cron_thread = threading.Thread(target=cron_checker_loop, daemon=True)
    cron_thread.start()
    print("[app] Price Monitor starting on port 5056")
    print("[app] Cron checker thread started (every 6 hours)")
    app.run(host="0.0.0.0", port=5056, debug=True, use_reloader=False)
