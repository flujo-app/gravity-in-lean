"""Write comparator/Challenge.lean and comparator.json from Audit.lean.

Every `example : Statement := proof` line of Audit.lean becomes `theorem proof : Statement := sorry`
in the challenge. (`connectionUnique`, whose own type is its fixed statement, cannot be asked: the
statement files the challenge imports already import its proof, so the name is taken.)

Usage:  python scripts/comparator/make_challenge.py           write both files
        python scripts/comparator/make_challenge.py --check   fail if either is out of date
"""
import json
import pathlib
import re
import sys

check = "--check" in sys.argv[1:]
root = pathlib.Path(__file__).resolve().parents[2]
audit = root.joinpath("Audit.lean").read_text(encoding="utf-8")
flat = re.sub(r"\s+", " ", audit)
pairs = re.findall(r"example : ([A-Za-z0-9_.]+(?:\.\{[0-9, ]+\})?) := ([A-Za-z0-9_.]+)", flat)

# Where each statement is fixed, read from the statement files themselves.
files = sorted(root.joinpath("GravityInLean", "Goals").glob("*.lean")) + [
    root.joinpath("GravityInLean", "Curved", "Goal.lean")]
where = {}
for f in files:
    for m in re.finditer(r"^def ([A-Za-z0-9_]+)", f.read_text(encoding="utf-8"), re.M):
        where.setdefault(m.group(1), f)

ORDER = ["Curved/Goal.lean", "Goals/Turns.lean", "Goals/ExactlyWhen.lean", "Goals/Tests.lean",
         "Goals/OneMass.lean", "Goals/Connection.lean", "Goals/EveryPoint.lean",
         "Goals/Global.lean", "Goals/GlobalComplete.lean"]
TITLE = {
    "Curved/Goal.lean": "Birkhoff's theorem with no coordinates",
    "Goals/Turns.lean": "The two results the standard library did not have",
    "Goals/ExactlyWhen.lean": "Both directions, and checks of their assumptions",
    "Goals/Tests.lean": "The 25 tests in which a definition must fail or hold",
    "Goals/OneMass.lean": "One mass for a connected region",
    "Goals/Connection.lean": "The connection of a length measure exists and is unique",
    "Goals/EveryPoint.lean": "Every point, the horizon included, and Kruskal's table",
    "Goals/Global.lean": "The whole space-time",
    "Goals/GlobalComplete.lean": "The proved statements of the classification file",
}

groups = {k: [] for k in ORDER}
for stmt, proof in pairs:
    base = stmt.split(".{")[0].split(".")[-1]
    rel = where[base].relative_to(root / "GravityInLean").as_posix()
    univ = ""
    m = re.search(r"\.\{([0-9, ]+)\}$", stmt)
    if m:  # universe-polymorphic statement: state it for all universes, as the proof is
        n = len(m.group(1).split(","))
        names = ["u", "v", "w", "u₁", "u₂"][:n]
        univ = ".{" + ", ".join(names) + "}"
        stmt = stmt.split(".{")[0] + univ
    groups[rel].append((proof + univ, stmt))

imports = sorted({"GravityInLean." + k.replace("/", ".").removesuffix(".lean") for k in ORDER})
out = ["/-", "Copyright (c) 2026 flujo-app. All rights reserved.",
       "Released under Apache 2.0 license as described in the file LICENSE.",
       "Authors: flujo-app", "-/"]
out += ["import " + i for i in imports]
total = sum(len(v) for v in groups.values())
out += ["", "/-!", "# The question for `lake comparator`", "",
        f"Every statement that `Audit.lean` checks against its proof: {total} in all. Each appears",
        "under the same full name as its proof in the project and with the statement fixed in `Goals/`",
        "or `Curved/Goal.lean`, but with `sorry` (a hole) in place of a proof. This file imports only",
        "the statement files (which bring the definitions and a few checks with them). It is written",
        "from the `example : Statement := proof` lines of `Audit.lean` by",
        "`scripts/comparator/make_challenge.py`, which also writes `comparator.json`; the workflow",
        "\"Compare statements\" fails when the two are out of date. `connectionUnique` cannot be asked",
        "here: the statement files already import its proof, so its name is taken.", "",
        "`lake comparator` (configured in `comparator.json` at the top of the repository) builds this",
        "file and `Audit.lean` inside its sandbox, and accepts only if each named result in `Audit.lean`",
        "has exactly the statement written here, rests on no assumption beyond `propext`,",
        "`Classical.choice` and `Quot.sound`, and passes the kernel and the other checkers.", "",
        "Because of the holes, this file is not built by `lake build`, and nothing in the project imports",
        "it: it lives in its own library (`Challenge` in `lakefile.toml`), outside the default targets.",
        "-/"]
names = []
for k in ORDER:
    if not groups[k]:
        continue
    out += ["", f"/-! ## {TITLE[k]} (`{k}`) -/"]
    for proof, stmt in groups[k]:
        names.append(proof.split(".{")[0])
        line = f"theorem {proof} : {stmt} :="
        out.append("")
        if len(line) <= 100:
            out.append(line)
        else:
            out += [f"theorem {proof} :", f"    {stmt} :="]
        out.append("  sorry")
cfg = {"challenge_module": "Challenge", "solution_module": "Audit", "theorem_names": names,
       "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
wanted = {
    root / "comparator" / "Challenge.lean": "\n".join(out) + "\n",
    root / "comparator.json": json.dumps(cfg, indent=2, ensure_ascii=False) + "\n",
}
if check:
    stale = [p.name for p, text in wanted.items()
             if not p.exists() or p.read_text(encoding="utf-8") != text]
    if stale:
        sys.exit(f"out of date with Audit.lean: {', '.join(stale)}; "
                 "run python scripts/comparator/make_challenge.py")
    print(f"comparator question matches Audit.lean ({total} statements)")
else:
    for p, text in wanted.items():
        p.write_text(text, encoding="utf-8", newline="\n")
    print(f"{total} statements written")
