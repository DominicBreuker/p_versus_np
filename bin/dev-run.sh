#!/bin/bash
# Run the Docker container for local development
# Usage: ./bin/dev-run.sh
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
IMAGE_NAME="p-vs-np-dev"
IMAGE_TAG="local"
cd "$REPO_ROOT"
echo "Starting Docker container from ${IMAGE_NAME}:${IMAGE_TAG}"
echo "Repository root mounted at /workspace"
echo "Use 'exit' to leave the container"
docker run -it --rm \
  -v "$REPO_ROOT/proofs:/workspace/proofs" \
  -v "$REPO_ROOT/lib:/workspace/lib" \
  -w /workspace \
  "${IMAGE_NAME}:${IMAGE_TAG}"
