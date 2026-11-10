"""Exercise live frozen scorer verdict logic without importing geometry or running a new experiment.
Exit 0 reproduces the documented limitation; it does NOT validate uncertified ranks.
"""
import ast
import copy
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
source = (root / "prereg/score_t1.py").read_text()
main = next(n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name == "main")
start = next(i for i,n in enumerate(main.body) if isinstance(n, ast.Assign)
             and any(isinstance(t, ast.Name) and t.id == "v" for t in n.targets))
stop = next(i for i,n in enumerate(main.body[start:], start) if isinstance(n, ast.Assign)
            and any(isinstance(t, ast.Subscript) and isinstance(t.value, ast.Name)
                    and t.value.id == "out" for t in n.targets))
code = compile(ast.Module(body=main.body[start:stop], type_ignores=[]), "live-verdict-block", "exec")
def verdict(data):
    scope = {"out": data}
    exec(code, scope)
    return scope["v"]

record = json.loads((root / "results/T1_score.json").read_text())
assert verdict(record) == record["verdicts"], "Live verdicts differ from recorded verdicts"
uncertified = copy.deepcopy(record)
uncertified["tiles"]["1"]["FR30"]["certified_G"] = False
v = verdict(uncertified)
assert v["H3"] == "pass" and v["all_ranks_certified_over_Q"] is False
print("REPRODUCED: H3 remains pass with uncertified G; certification is only a separate flag.")
empty = copy.deepcopy(record)
empty["tiles"] = {}
v = verdict(empty)
assert v["H1"] == "pass on run levels; incomplete"
print("REPRODUCED: no tile levels can produce 'pass on run levels; incomplete' via vacuous all().")
print("Recorded complete certified run verdicts match live logic; historical run not changed.")
