#!/bin/bash
# Build the Docker image for local development
# Usage: ./bin/dev-build.sh
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
IMAGE_NAME="p-vs-np-dev"
IMAGE_TAG="local"
cd "$REPO_ROOT"
echo "Building Docker image: ${IMAGE_NAME}:${IMAGE_TAG}"
docker build -t "${IMAGE_NAME}:${IMAGE_TAG}" .
echo "Build complete!"
echo "Run with: ./bin/dev-run.sh"
