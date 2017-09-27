FROM fpco/stack-build:lts-8.9
RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell -b popl18
RUN cd liquidhaskell && stack test --fast liquidhaskell --system-ghc
WORKDIR liquidhaskell
CMD stack test --fast liquidhaskell --system-ghc
