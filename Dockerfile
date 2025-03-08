# Use an official Ubuntu as a parent image
FROM debian:bookworm-slim

# Set environment variables for non-interactive install
ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies for OCaml and Rust
RUN apt-get update && apt-get install -y \
    curl \
    software-properties-common \
    build-essential \
    libssl-dev \
    wget \
    opam \
    libgmp-dev \
    pkg-config \
    libsqlite3-dev \
    && rm -rf /var/lib/apt/lists/*

RUN ARCH=$(uname -m) && \
    if [ "$ARCH" = "x86_64" ]; then Z3_ARCH="x64-glibc-2.35"; \
    elif [ "$ARCH" = "aarch64" ]; then Z3_ARCH="arm64-glibc-2.34"; \
    else echo "Unsupported architecture: $ARCH" && exit 1; fi && \
    \
    # Get latest Z3 release
    LATEST_Z3_VERSION=$(curl -s https://api.github.com/repos/Z3Prover/z3/releases/latest | grep "tag_name" | cut -d '"' -f 4) && \
    curl -L -o z3.zip "https://github.com/Z3Prover/z3/releases/download/z3-4.14.0/z3-4.14.0-$Z3_ARCH.zip" && \
    unzip z3.zip -d /opt/z3 && \
    rm z3.zip && \
    echo $Z3_ARCH && \
    ls /opt/z3 && \
    ln -s /opt/z3/z3-4.14.0-$Z3_ARCH/bin/z3 /usr/local/bin/z3

RUN z3 --version

# Install OPAM and OCaml
RUN eval $(opam env)
RUN opam init -a --disable-sandboxing --bare
RUN opam switch create gillian-rust --packages=ocaml-variants.5.2.1+options,ocaml-option-flambda
RUN eval $(opam env --set-switch=gillian-rust)

# Install Rust with the specified toolchain
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y \
    && ~/.cargo/bin/rustup toolchain install nightly-2024-05-10 \
    && ~/.cargo/bin/rustup default nightly-2024-05-10

# Set environment variables for Rust
ENV PATH="/root/.cargo/bin:${PATH}"

# Verify installations
RUN opam --version && rustc --version

# Install Creusot
RUN git clone https://github.com/creusot-rs/creusot
WORKDIR /creusot
RUN git checkout tags/v0.4.0
RUN echo "--external z3" > INSTALL.opts
RUN ./INSTALL

# Set the working directory
WORKDIR /app

# Copy your application code to the container
COPY . /app

RUN cargo build
RUN cargo test --test ui -- --bless

WORKDIR /app/Gillian-Rust
RUN opam install . -y

WORKDIR /app

# Command to run your application (modify as needed)
CMD ["bash", "-i"]
