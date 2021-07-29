# Building and deploying the documentation

One-off:

```
$ sudo apt-get install python3 pip3  # or equivalent
$ pip3 install mkdocs-material mkdocs-awesome-pages-plugin
```

after that to view the documents locally run:

```
$ mkdocs serve
```

from the directory that this README is in.

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

## Adding blog posts

* Write your post in markdown (+HTML)
* Put it in the `docs/blogposts/` directory
* Datestamp the filename with `YYYY-MM-DD-`

The new blogpost will then be automatically added to the site at next deploy.
