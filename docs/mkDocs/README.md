# Building and deploying the documentation

To build the documentation, first setup `python3` and related packages

```
$ cd docs/mkDocs
$ python3 -m pip install --upgrade pip
$ python3 get-pip.py
$ pip3 install mkdocs pygments Pygmentize mkdocs-bootswatch
```

after that to view the documents locally run:

```
mkDocs serve
```

## Strict mode

It's recommended to run `mkDocs serve` with the _strict_ option (i.e. `-s`) to ensure no broken links are
present in the generated docs:

```
mkDocs serve -s
```

## Publishing

To push to github you can simply run:

```
mkdocs gh-deploy
```
