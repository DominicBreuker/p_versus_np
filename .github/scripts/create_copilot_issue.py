#!/usr/bin/env python3
"""Create a GitHub issue and assign a Copilot coding agent to it."""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

import requests


GITHUB_API = "https://api.github.com"
GRAPHQL_URL = f"{GITHUB_API}/graphql"
REQUESTS_TIMEOUT = 20


def get_headers(token: str) -> dict[str, str]:
    return {
        "Authorization": f"Bearer {token}",
        "Accept": "application/vnd.github+json",
    }


def load_issue_body(filepath: str) -> str:
    path = Path(filepath)
    if not path.exists():
        raise FileNotFoundError(f"Issue body file not found: {filepath}")
    return path.read_text(encoding="utf-8")


def parse_vars(var_list: list[str] | None) -> dict[str, str]:
    """Parse repeated --var key=value arguments into a dict."""
    result: dict[str, str] = {}
    for item in var_list or []:
        if "=" not in item:
            raise ValueError(f"Invalid variable format: {item}")
        key, value = item.split("=", 1)
        result[key.strip()] = value.strip()
    return result


def render_template(body: str, vars_dict: dict[str, str]) -> str:
    """Replace {{ var }} in body with values from vars_dict."""
    keys = set(re.findall(r"{{\s*([\w.-]+)\s*}}", body))
    missing = sorted(key for key in keys if key not in vars_dict)
    if missing:
        raise ValueError(f"Missing template variables: {', '.join(missing)}")

    def replacer(match: re.Match[str]) -> str:
        key = match.group(1).strip()
        return vars_dict[key]

    return re.sub(r"{{\s*([\w.-]+)\s*}}", replacer, body)


def create_issue(token: str, owner: str, repo: str, title: str, body: str) -> dict:
    response = requests.post(
        f"{GITHUB_API}/repos/{owner}/{repo}/issues",
        headers=get_headers(token),
        json={"title": title, "body": body},
        timeout=REQUESTS_TIMEOUT,
    )
    response.raise_for_status()
    return response.json()


def get_copilot_actor_id(token: str, owner: str, repo: str) -> str:
    query = """
    query($owner:String!, $repo:String!) {
      repository(owner:$owner, name:$repo) {
        suggestedActors(capabilities:[CAN_BE_ASSIGNED], first:20) {
          nodes {
            login
            ... on Bot { id }
          }
        }
      }
    }
    """
    response = requests.post(
        GRAPHQL_URL,
        headers=get_headers(token),
        json={"query": query, "variables": {"owner": owner, "repo": repo}},
        timeout=REQUESTS_TIMEOUT,
    )
    response.raise_for_status()
    payload = response.json()
    nodes = payload["data"]["repository"]["suggestedActors"]["nodes"]
    bot = next((node for node in nodes if node["login"].startswith("copilot-")), None)
    if not bot:
        raise RuntimeError("Copilot agent not found in suggestedActors")
    return bot["id"]


def get_issue_global_id(token: str, owner: str, repo: str, issue_number: int) -> str:
    query = """
    query($owner:String!, $repo:String!, $num:Int!) {
      repository(owner:$owner, name:$repo) {
        issue(number:$num) {
          id
        }
      }
    }
    """
    response = requests.post(
        GRAPHQL_URL,
        headers=get_headers(token),
        json={"query": query, "variables": {"owner": owner, "repo": repo, "num": issue_number}},
        timeout=REQUESTS_TIMEOUT,
    )
    response.raise_for_status()
    payload = response.json()
    return payload["data"]["repository"]["issue"]["id"]


def assign_actor_to_issue(token: str, issue_id: str, actor_id: str) -> list[str]:
    mutation = """
    mutation($iid:ID!, $aid:ID!) {
      replaceActorsForAssignable(input:{assignableId:$iid, actorIds:[$aid]}) {
        assignable {
          ... on Issue {
            assignees(first:5) {
              nodes { login }
            }
          }
        }
      }
    }
    """
    response = requests.post(
        GRAPHQL_URL,
        headers=get_headers(token),
        json={"query": mutation, "variables": {"iid": issue_id, "aid": actor_id}},
        timeout=REQUESTS_TIMEOUT,
    )
    response.raise_for_status()
    payload = response.json()
    nodes = payload["data"]["replaceActorsForAssignable"]["assignable"]["assignees"]["nodes"]
    return [node["login"] for node in nodes]


def append_github_output(name: str, value: str) -> None:
    github_output = os.environ.get("GITHUB_OUTPUT")
    if not github_output:
        return
    with open(github_output, "a", encoding="utf-8") as fh:
        fh.write(f"{name}={value}\n")


def main() -> None:
    parser = argparse.ArgumentParser(description="Create GitHub issue and assign Copilot agent")
    parser.add_argument("owner", help="Repository owner")
    parser.add_argument("repo", help="Repository name")
    parser.add_argument("issue_file", help="Path to the Markdown file containing issue content")
    parser.add_argument("--title", required=True, help="Issue title")
    parser.add_argument(
        "--token",
        default=os.getenv("GH_PAT") or os.getenv("GITHUB_TOKEN"),
        help="GitHub token (or set GH_PAT / GITHUB_TOKEN)",
    )
    parser.add_argument(
        "--var",
        action="append",
        help="Template variables in the form key=value (can be repeated)",
    )
    args = parser.parse_args()

    if not args.token:
        sys.exit("❌ GitHub token not provided. Use --token or set GH_PAT / GITHUB_TOKEN.")

    try:
        body_template = load_issue_body(args.issue_file)
        body = render_template(body_template, parse_vars(args.var))
        issue = create_issue(args.token, args.owner, args.repo, args.title, body)
        print(f"📝 Created issue #{issue['number']}: {issue['html_url']}")

        actor_id = get_copilot_actor_id(args.token, args.owner, args.repo)
        print(f"🤖 Copilot agent ID: {actor_id}")

        issue_gid = get_issue_global_id(args.token, args.owner, args.repo, issue["number"])
        assignees = assign_actor_to_issue(args.token, issue_gid, actor_id)
        print(f"✅ Assigned Copilot: {assignees}")

        append_github_output("issue_number", str(issue["number"]))
        append_github_output("issue_url", issue["html_url"])
        append_github_output("assignees", ",".join(assignees))
    except Exception as exc:  # pragma: no cover - workflow-facing error path
        sys.exit(f"❌ Error: {exc}")


if __name__ == "__main__":
    main()
