# Practical Verification of The Inductive Graph Library

## Dependencies

You need to have [Agda] and [agda2hs] installed.
To build agda2hs, install `cabal` and run the following commands:

```
git clone git@github.com:agda/agda2hs.git
cd agda2hs
make install
```

The binary `agda2hs` should now be available in `~/.cabal/bin/`. Make sure this
directory is in your `$PATH` environment variable. You can add the following in
your shell config (`~/.zshrc` or `.bashrc`:

```
export PATH=~/.cabal/bin:$PATH
```

## Project

In this research project the Inductive Graph Library from Haskell is ported to Haskell, verified with Agda and ported back with agda2hs. However, the verification process is not complete.

In order to use the Agda version of the Inductive Graph and the additional data libraries from your Agda code, you need
to tell Agda where to locate the library. Inside the file `~/.agda/libraries`,
add the following line:

```
/your/path/to/inductiveGraph.agda-lib
```

The Inductive Graph can be ported back to Haskell by running make. This compiles the Inductive Graph to Haskell and is then checked by GHC.

This project also contains the `PatricaTree` and the `PatriciaGraph`.

`commonSubset.agda` contains simple examples of Agda functions to see if agda2hs can compile these functions to Haskell.
