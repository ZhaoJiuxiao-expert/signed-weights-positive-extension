"""Fresh Lean kernel builds and an exact, independent check of Section 5."""

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parent
MODULES = ["RampEndpoint", "PositiveWindow", "GramCertificate", "Main"]
STANDARD = {"propext", "Quot.sound", "Classical.choice"}


def example():
    n_target, q, cutoff, c = 64, 3847, 8, 2
    x = n_target - 2
    assert q > x*x and all(q % d for d in range(2, isqrt(q)+1))
    mu = [1] * (n_target+1)
    for p in range(2, n_target+1):
        if any(p % d == 0 for d in range(2, isqrt(p)+1)):
            continue
        for n in range(p, n_target+1, p):
            mu[n] *= -1
        for n in range(p*p, n_target+1, p*p):
            mu[n] = 0
    weights = {}
    for n in range(2, x+1):
        m = n_target - n
        if n_target <= 3*n < 2*n_target and gcd(n, n_target) == 1 and m % 2:
            value = sum(mu[d] for d in range(cutoff+1, m+1) if m % d == 0)
            if value:
                weights[n] = value
    assert weights == {23:-1, 27:-1, 29:1, 33:-1, 35:-1, 41:-1}
    amplitudes = {1:c, **weights}
    def coordinate(k):
        return Fraction(sum(a*amplitudes.get(k*b % q, 0) for b,a in amplitudes.items()), c)
    assert coordinate(1) == 5
    assert all(coordinate(k) == weights.get(k,0) for k in range(2,x+1))
    principal = Fraction(sum(amplitudes.values())**2, c*(q-1))
    assert principal == Fraction(1,1923)
    return {"N":n_target,"X":x,"q":q,"c":c,"weight":weights,
            "spectral_mass":str(coordinate(1)),"principal_coefficient":str(principal),
            "coordinates_2_through_X":x-1}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"))
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if not args.lean:
        parser.error("Add Lean 4.13.0 to PATH or supply --lean.")
    compiler = str(Path(args.lean).resolve())
    version = subprocess.check_output([compiler,"--version"], text=True).strip()
    if "version 4.13.0," not in version:
        parser.error("Use the version pinned in lean-toolchain.")
    report = {"toolchain":version,"modules":{},"example":example()}
    with TemporaryDirectory(prefix="positive-window-") as output_dir:
        for name in MODULES:
            source = ROOT / (name+".lean")
            source_data = source.read_bytes()
            n_expected = len(re.findall(rb"(?m)^#print axioms ", source_data))
            result = subprocess.run(
                [compiler, "-o", str(Path(output_dir)/(name+".olean")), str(source)],
                cwd=ROOT, env=dict(os.environ, LEAN_PATH=output_dir),
                capture_output=True, text=True, encoding="utf-8")
            output = result.stdout + result.stderr
            audit_sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
            n_checked = len(audit_sets) + output.count("does not depend on any axioms")
            used = {a.strip() for row in audit_sets for a in row.split(",") if a.strip()}
            if (result.returncode or "warning:" in output or "sorryAx" in output
                    or not n_expected or n_expected != n_checked or used - STANDARD):
                raise RuntimeError(f"Verification failed for {name}:\n{output}")
            report["modules"][name] = {"sha256":sha256(source_data).hexdigest(),
                "checked":n_checked,"axioms":sorted(used),"kernel_output":output.strip()}
    report["status"] = "passed"
    encoded = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.out:
        args.out.write_text(encoded, encoding="utf-8")
    print(f"{len(MODULES)} modules, {sum(v['checked'] for v in report['modules'].values())} "
          "axiom audits; Section 5 exact arithmetic check passed.")


if __name__ == "__main__":
    main()
