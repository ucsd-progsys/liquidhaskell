# Building and deploying the documentation

To build the documentation, first setup `python3` and related packages.

You need `python3`, `pip3`, and `mkdocs` pre-installed (e.g. via `apt`).

```
$ cd docs/mkDocs
$ pip3 install mkdocs pygments mkdocs-bootswatch
```

after that to view the documents locally run:

```
mkdocs serve
```

## Strict mode

It's recommended to run `mkDocs serve` with the _strict_ option (i.e. `-s`) to ensure no broken links are
present in the generated docs:

```
mkdocs serve -s
```

## Publishing

To push to github you can simply run:

```
mkdocs gh-deploy
```
