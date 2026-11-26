"""Scan a built Lean project from named theorem roots. Write reports to a new directory."""
import argparse
import gzip
import json
from pathlib import Path
import subprocess
import tempfile

from coarse_first import module_islands
from gapped_runs import scan
from root_paths import linked_reachability
from unreferenced_family import source_declarations


def newly_outside(before, after):
    """Previously reachable project declarations absent from the new rooted graph."""
    return sorted((module, name) for name, (module, _) in before
                  if name not in after or after[name][0] != module)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="Lake project directory")
    parser.add_argument("output", type=Path, help="new directory outside the source tree")
    parser.add_argument("--root", action="append", required=True, help="fully qualified theorem, repeatable")
    parser.add_argument("--root-module", default="Main", help="module importing every selected theorem")
    parser.add_argument("--source", default="src", help="project-relative Lean source directory")
    parser.add_argument("--library", default=".lake/build/lib/lean", help="matching compiled library")
    parser.add_argument("--before", type=Path, help="previous report for the same roots, before the selected rewrite")
    args = parser.parse_args()
    project = args.project.resolve()
    source = (project / args.source).resolve()
    library = project / args.library
    output = args.output.resolve()
    modules = {'.'.join(f.relative_to(source).with_suffix('').parts): f
               for f in sorted(source.rglob('*.lean'))
               if not {'.lake', '.git'}.intersection(f.relative_to(source).parts)}
    if args.root_module not in modules:
        parser.error("root module is missing from the source directory")
    if output.exists() or output.is_relative_to(source):
        parser.error("choose a new output directory outside the source tree")
    roots = list(dict.fromkeys(args.root))
    request = dict(rootModule=args.root_module, modules=list(modules), roots=roots)
    extractor = Path(__file__).with_name("LinkedRoots.lean").resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=output.parent) as scratch:
        stage = Path(scratch) / "report"
        stage.mkdir()
        graph = {}
        with (stage / "graph.jsonl.gz").open("wb") as raw:
            with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as packed:
                run = subprocess.run(["lake", "env", "lean", "-j1", "--run", str(extractor)],
                                     cwd=project, input=json.dumps(request), text=True,
                                     stdout=subprocess.PIPE, check=True)
                for name, (module, edges) in sorted(map(json.loads, run.stdout.splitlines())):
                    graph[name] = module, sorted(edges)
                    packed.write((json.dumps([name, graph[name]]) + "\n").encode())
        imports, outside = {}, []
        for module, path in modules.items():
            info = json.loads((library / path.relative_to(source).with_suffix(".ilean")).read_bytes())
            if info["module"] != module:
                raise ValueError(f"source and compiler module differ for {module}")
            imports[module] = [imp[0] for imp in info["directImports"] if imp[0] in modules]
            for name, decl in source_declarations(path, info).items():
                if name not in graph or graph[name][0] != module:
                    outside.append(dict(module=module, name=name, first=decl["first_line"], last=decl["last_line"]))
        groups = module_islands(imports, [args.root_module])
        outside.sort(key=lambda r: (r["first"] - r["last"], r["module"], r["name"]))
        candidates = scan(source, library, graph, roots)
        targets = sorted({r[k] for r in candidates["rows"] for k in ("left", "right")})
        _, paths = linked_reachability(graph.items(), roots, targets)
        report = dict(roots=roots, modules=len(modules), reachable_declarations=len(graph),
                      module_islands=groups, outside_roots=outside, fragments=candidates, paths=paths)
        if args.before:
            old = json.loads((args.before / "report.json").read_bytes())
            if set(old["roots"]) != set(roots):
                parser.error("--before must cover the same theorem roots")
            with gzip.open(args.before / "graph.jsonl.gz", "rt") as stream:
                report["newly_outside_roots"] = newly_outside(map(json.loads, stream), graph)
        (stage / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        stage.rename(output)
    print(f"{len(modules)} modules, {len(graph)} reachable declarations, "
          f"{len(outside)} located theorems outside the roots, {len(candidates['rows'])} fragment pairs")


if __name__ == "__main__":
    main()
