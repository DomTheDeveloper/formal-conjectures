FROM ubuntu:24.04

ARG NB_USER=jovyan
ARG NB_UID=1000
ENV DEBIAN_FRONTEND=noninteractive

USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git python3 python3-pip zstd xz-utils \
    && rm -rf /var/lib/apt/lists/* \
    && python3 -m pip install --break-system-packages --no-cache-dir \
      jupyterhub notebook jupyterlab \
    && groupadd --gid ${NB_UID} ${NB_USER} \
    && useradd --uid ${NB_UID} --gid ${NB_UID} --create-home --shell /bin/bash ${NB_USER}

ENV HOME=/home/${NB_USER}
COPY --chown=${NB_UID}:${NB_UID} . ${HOME}/project
USER ${NB_USER}
WORKDIR ${HOME}/project

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
      sh -s -- -y --default-toolchain none
ENV PATH=${HOME}/.elan/bin:${PATH}

RUN chmod +x binder/run-audit.sh && binder/run-audit.sh

ENTRYPOINT []
CMD ["jupyter", "lab", "--ip=0.0.0.0", "--no-browser"]
