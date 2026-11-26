"""Read the default branch, same-file open PR patches, and the author's PR checks with gh."""
import argparse
import json
import subprocess


def gh(*args):
    return json.loads(subprocess.check_output(["gh", *args]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", help="OWNER/REPO")
    parser.add_argument("files", nargs="+", help="proposed repository-relative paths")
    parser.add_argument("--author", help="GitHub login for the author's check summary")
    args = parser.parse_args()
    repo = args.repository
    wanted = set(args.files)
    owner, name = repo.split("/", 1)
    default_query = """query($owner:String!,$name:String!) {
      repository(owner:$owner,name:$name){defaultBranchRef{name target{oid}}}
    }"""
    endpoint = ["api", "graphql", "-f", "owner=" + owner, "-f", "name=" + name]
    base = gh(*endpoint, "-f", "query=" + default_query)["data"]["repository"]["defaultBranchRef"]
    query = """query($owner:String!,$name:String!,$base:String!,$endCursor:String) {
      repository(owner:$owner,name:$name){pullRequests(states:OPEN,first:50,after:$endCursor,
        baseRefName:$base){pageInfo{hasNextPage endCursor} nodes{
        number url headRefOid headRefName files(first:100){pageInfo{hasNextPage} nodes{path changeType}}
      }}}
    }"""
    pages = gh(*endpoint, "--paginate", "--slurp", "-f", "base=" + base["name"], "-f", "query=" + query)
    prs = [p for page in pages for p in page["data"]["repository"]["pullRequests"]["nodes"]]
    overlaps = []
    for pr in prs:
        listed = pr["files"]
        if not (listed["pageInfo"]["hasNextPage"] or pr["headRefName"].startswith("batch/")
                or any(f["changeType"] == "RENAMED" or f["path"] in wanted for f in listed["nodes"])):
            continue
        changes = gh("api", "--paginate", "--slurp", f"repos/{repo}/pulls/{pr['number']}/files?per_page=100")
        hits = [f for page in changes for f in page if wanted.intersection((f["filename"], f.get("previous_filename")))]
        if hits:
            overlaps.append(dict(number=pr["number"], head=pr["headRefOid"], url=pr["url"],
                                 files=[{k: f.get(k) for k in ("filename", "previous_filename", "status", "patch")}
                                        for f in hits]))
    result = dict(base=base, open_prs=len(prs), overlaps=overlaps)
    if args.author:
        result["author_prs"] = gh("pr", "list", "--repo", repo, "--state", "open", "--author", args.author,
                                  "--base", base["name"], "--limit", "1000", "--json",
                                  "number,url,headRefOid,mergeable,reviewDecision,statusCheckRollup")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
