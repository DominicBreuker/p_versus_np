# Dockerfile for local Lean 4 development environment
FROM ubuntu:22.04

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    git \
    gcc \
    g++ \
    make \
    cmake \
    libssl-dev \
    pkg-config \
    python3 \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /workspace

# Create a non-root user for development
RUN useradd -m -u 30000 devuser && \
    mkdir -p /workspace && \
    chown devuser:devuser /workspace
USER devuser

# Install elan (Lean version manager) as devuser
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
# Add elan to PATH (now installed in /home/devuser/.elan/bin)
ENV PATH="/home/devuser/.elan/bin:${PATH}"

# Install specific Lean toolchain
RUN elan toolchain install leanprover/lean4:v4.30.0-rc2
RUN elan default leanprover/lean4:v4.30.0-rc2

# Install lake
RUN lake --version || (curl -sSfL https://raw.githubusercontent.com/leanprover-community/lake/main/scripts/install.sh | sh)

COPY . .

RUN ls -lah

RUN lake build

RUN ls -lah

# Default command when container starts
CMD ["bash"]
