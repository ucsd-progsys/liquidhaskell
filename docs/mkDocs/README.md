## Deploying the Documentation

To build the documentation, first setup `python3` and related packages

```
$ cd docs/mkDocs
$ python3 -m pip install --upgrade pip
$ python3 get-pip.py
$ pip3 install mkdocs pygments Pygmentize mkdocs-bootswatch
```

after that to view the documents locally do

```
$ mkDocs serve
```

to push to github you do

mkDocs gh-deploy

```
$ mkdocs gh-deploy
```
