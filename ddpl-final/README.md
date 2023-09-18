# Set Up
- OS: Ubuntu  20.04

```
 $ sudo apt-get install libgc-dev libgmp-dev gcc-7 uthash-dev software-properties-common
 $ sudo add-apt-repository ppa:hvr/ghc && sudo apt update && sudo apt install ghc-9.0.1 cabal-install-3.4
 $export PATH="/opt/ghc/bin:$PATH" 
```
- Install haskell stack
```
donzho@LAPTOP-7IE4DBQH ~ % stack --version
Version 2.9.3, Git revision 6cf638947a863f49857f9cfbf72a38a48b183e7e x86_64 hpack-0.35.1
```
- BUild steps
  1. run "stack build" from root directory(.\ddpl-final)
   % stack build
```
gibbon-0.2: unregistering (local file changes: README.md)
gibbon> configure (lib + exe)
Configuring gibbon-0.2...
gibbon> build (lib + exe)
Preprocessing library for gibbon-0.2..
Building library for gibbon-0.2..
[ 1 of 13] Compiling Gibbon.DynFlags
[ 2 of 13] Compiling Gibbon.Common
[ 3 of 13] Compiling Gibbon.Language.Syntax
```
  2. run stack test from root directory