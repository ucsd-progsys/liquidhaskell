
## Mirroring modules for the liquid ecosystem

We provide a fairly simple tool (under the form of an Haskell executable) to make the process of
generating "mirror modules" easy. This need might arise when developing new packages containing only refinemnents
for existing packages. These modules are usually meant to be considered \"drop in\", which means they should
expose the very same modules the original package provided. For big and rich packages, this process can be
tedious to do by hand, especially if only a handful of modules contains refinemnents. This is where this
tool comes in hand.

The tool for now can be built only if the `mirror-modules-helper` flag is passed 
(and it's **not** turned on by default) to avoid pulling unnecessary dependencies when we build
the `liquidhaskell` library. We can in principle move this into a standalone package, in the future.

### Installation instructions (stack)

```
stack build --flag liquidhaskell:mirror-modules-helper
```

### Usage

The tool accepts the following options:

```
stack exec mirror-modules -- --help

Usage: mirror-modules [--unsafe-override-files] (-l|--modules-list ARG)
                      (-p|--mirror-package-name ARG) (-i|--target ARG)
  Create modules to be used in mirror packages.

Available options:
  --unsafe-override-files  Overrides an Haskell module if already present in the
                           folder.
  -l,--modules-list ARG    The path to a file containing a newline-separated
                           list of modules to mirror.
  -p,--mirror-package-name ARG
                           The name of the mirror package we are targeting.
                           (example: liquid-foo)
  -i,--target ARG          The path to the root of the module hierarchy for the
                           target package. (example: liquid-foo/src)
  -h,--help                Show this help text
```


The tool is faily simple and eschew more sophisticated mechanisms (like automatically pulling the mirrored
package from Hackage and extract the exposed-modules from the parsed Cabal manifest), so it accepts a file
with the full list of exposed modules of the mirrored package (which can be copied and pasted from the Cabal
manifest directly) and it's smart enough to figure out which modules needs mirroring. The user can decide
to unsafely override existing modules by passing the `--unsafe-override-files` option as input.
Last but not least, we require the name of the mirror package (e.g. `liquid-foo`) as well as the path
(relative or absolute) where the source files are (e.g. `liquid-foo/src`).

### Example (liquid-base)

For example, this is how we can mirror all the packages from `base` into `liquid-base`:

```
stack exec mirror-modules -- -l ../packages.txt -p liquid-base -i liquid-base/src/
```

Where `packages.txt` contains the newline-separated list of all the `exposed-modules` from `base`.
