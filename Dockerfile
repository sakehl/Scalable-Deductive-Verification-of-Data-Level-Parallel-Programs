FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    HOME=/root \
    PATH=/root/.elan/bin:/vercors:${PATH}

WORKDIR /opt/cavartefact

RUN mkdir -p /opt/cavartefact/dependencies
RUN mkdir -p /root/.cache/coursier /root/.cache/mill /root/.elan

# RUN apt-get update
# RUN apt-get texlive-fonts-recommended texlive-latex-base texlive-base python3-numpy python3-matplotlib
# RUN apt-get elan openjdk-17-jre-headless git curl

# RUN apt-get --print-uris install texlive-fonts-recommended texlive-latex-base texlive-base python3-numpy python3-matplotlib   elan openjdk-17-jre-headless git curl | grep -oP "(?<=').*(?=')" > package.deps

COPY ./dependencies.tar.gz /opt/cavartefact/dependencies.tar.gz
RUN tar -xzf /opt/cavartefact/dependencies.tar.gz -C /opt/cavartefact
RUN cd /opt/cavartefact/dependencies/packages && apt-get install -y ./*.deb

RUN update-alternatives --set java /usr/lib/jvm/java-17-openjdk-amd64/bin/java

RUN cp -a /opt/cavartefact/dependencies/coursier/. /root/.cache/coursier/
RUN cp -a /opt/cavartefact/dependencies/mill/. /root/.cache/mill/

COPY ./vercors /opt/cavartefact/vercors
RUN cd /opt/cavartefact/vercors && bin/vct --version
RUN ln -sf /opt/cavartefact/vercors/bin /vercors

COPY ./LeanProof /opt/cavartefact/LeanProof
RUN tar -xzf /opt/cavartefact/dependencies/QuantifierLean-elan.tar.gz -C /root/.elan
RUN tar -xzf /opt/cavartefact/dependencies/QuantifierLean-lake.tar.gz -C /opt/cavartefact/LeanProof
RUN chown -R root:root /root/.elan /opt/cavartefact/LeanProof

RUN cd /opt/cavartefact/LeanProof && lake build
RUN rm -rf /opt/cavartefact/dependencies /opt/cavartefact/dependencies.tar.gz

WORKDIR /opt/cavartefact

CMD ["/bin/bash"]