FROM fpco/stack-build:lts-8.9
RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell -b popl18
RUN cd liquidhaskell && echo "system-ghc: true" >> stack.yaml && stack test --fast liquidhaskell
WORKDIR liquidhaskell
CMD stack test --fast liquidhaskell
