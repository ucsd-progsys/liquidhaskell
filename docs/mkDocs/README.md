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

This is a bit more involved than other edits, since an intermediate step is needed to generate fancy tooltips on code blocks.

To add a blog post;

1. Write your blogpost in Literate Haskell
2. Archive your blogpost's source code in `https://github.com/ucsd-progsys/liquidhaskell/tree/develop/docs/blog`, date-stamped with the `YYYY-MM-DD-` prefix.
3. Use LiquidHaskell to generate a corresponding `.markdown` file
    * The code blocks in this file are annotated with Liquid Types & Errors, for easier reading
4. Use `pandoc` to remove any non-markdown/HTML markup (e.g. latex)
5. Put the final output in the `docs/blogposts` subdirectory of this repository.
6. Rebuild/redeploy the docs as usual

This is not automated for two reasons: (1) performance and (2) so that old blogposts (with out-of-date syntax) don't break the re-build of the docs
