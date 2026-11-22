"""Index the author's pinned source archive. Only data under src/ is read."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import tarfile
import zlib


ARCHIVE_HASH = "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"
IMPORT = re.compile(rb"(?m)^[ \t]*(?:(?:public|private|meta|all)[ \t]+)*import[ \t]+([^\r\n]+)")
MODULE = re.compile(rb"[A-Za-z_][A-Za-z0-9_'.]*")
THEMES = [
    "Goldbach", "vonMangoldt", "LFunction", "DedekindZeta", "Behrend",
    "Vandiver", "Stepanov", "Linnik", "Iwasawa", "Kummer", "Seesaw",
]


def run(archive, database, report):
    with archive.open("rb") as handle:
        if hashlib.file_digest(handle, "sha256").hexdigest() != ARCHIVE_HASH:
            raise ValueError("Unexpected archive digest")
    if database.exists():
        raise FileExistsError(f"Use a fresh index path: {database}")
    conn = sqlite3.connect(database)
    conn.execute("CREATE TABLE source (module TEXT PRIMARY KEY, lines INTEGER, body BLOB)")
    sections = {}
    occurrences = Counter()
    imports = {}
    with tarfile.open(archive, "r|gz", bufsize=1024*1024) as tar:
        for member in tar:
            parts = member.name.strip("/").split("/")
            if not member.isfile() or "src" not in parts or not parts[-1].endswith(".lean"):
                continue
            rel = parts[parts.index("src")+1:]
            module = ".".join(rel)[:-5]
            data = tar.extractfile(member).read()
            lines = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
            stats = sections.setdefault(rel[0] if len(rel) > 1 else "(root)", Counter())
            stats.update(files=1, lines=lines, bytes=len(data))
            conn.execute("INSERT INTO source VALUES (?, ?, ?)",
                         (module, lines, zlib.compress(data, level=1)))
            refs = []
            for line in IMPORT.findall(data):
                for token in line.split(b"--")[0].split():
                    if not MODULE.fullmatch(token):
                        break
                    refs.append(token.decode())
            imports[module] = refs
            corpus = module.lower().encode() + b"\n" + data.lower()
            for word in THEMES:
                if word.lower().encode() in corpus:
                    occurrences[word] += 1
    conn.commit()
    conn.close()
    reachable = set()
    pending = ["Main"]
    while pending:
        module = pending.pop()
        if module not in reachable and module in imports:
            reachable.add(module)
            pending.extend(imports[module])
    summary = {
        "archive_sha256": ARCHIVE_HASH, "archive_bytes": archive.stat().st_size,
        "files": len(imports), "physical_lines": sum(v["lines"] for v in sections.values()),
        "source_bytes": sum(v["bytes"] for v in sections.values()),
        "source_modules_reachable_via_textual_imports_from_Main": len(reachable),
        "sections": dict(sorted(sections.items())),
        "modules_matching_casefolded_literal_in_path_or_text": dict(sorted(occurrences.items())),
    }
    report.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, ensure_ascii=True), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("database", type=Path, help="new temporary SQLite database for source queries")
    parser.add_argument("report", type=Path, help="output JSON")
    args = parser.parse_args()
    run(args.archive, args.database, args.report)
