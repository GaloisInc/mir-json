FROM ubuntu:22.04 AS build

RUN apt-get update && \
    apt-get install -y build-essential curl && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN useradd -m mir-json
COPY --chown=mir-json:mir-json . /mir-json
USER mir-json
WORKDIR /mir-json

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    PATH=/home/mir-json/.cargo/bin:$PATH
ENV RUST_TOOLCHAIN="nightly-2023-01-23"
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y --profile minimal --default-toolchain ${RUST_TOOLCHAIN}
RUN rustup component add --toolchain ${RUST_TOOLCHAIN} rustc-dev
RUN cargo install --locked && \
    mir-json-translate-libs

FROM ubuntu:22.04

RUN apt-get update && \
    apt-get install -y build-essential ca-certificates && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

COPY --from=build /mir-json/rlibs /mir-json/rlibs
COPY --from=build /home/mir-json/.cargo/bin /home/mir-json/.cargo/bin
COPY --from=build /home/mir-json/.rustup /home/mir-json/.rustup

RUN useradd -m mir-json && chown -R mir-json:mir-json /home/mir-json
USER mir-json

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    PATH=/home/mir-json/.cargo/bin:$PATH \
    CRUX_RUST_LIBRARY_PATH=/mir-json/rlibs

ENTRYPOINT ["/usr/bin/bash"]
