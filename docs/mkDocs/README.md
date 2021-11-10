# Building and deploying the documentation

One-off:

```
$ sudo apt-get install python3 pip3 # or equivalent
$ pip3 install mkdocs-material mkdocs-awesome-pages-plugin git+https://github.com/jldiaz/mkdocs-plugin-tags.git
```

after that to view the documents locally run:

```
$ mkdocs serve
```

from the directory that this README is in.

## Options for `mkdocs serve`

`mkdocs serve` supports serveral useful command-line flags, e.g.:

* `mkdocs serve -s` (refuse to build docs with broken links)
* `mkdocs serve -a 0.0.0.0:8000` (allow connections from LAN -- necessary if running in container/vm)

For more options, see `mkdocs serve --help`

## Publishing

Documentation is *automatically* published to GitHub pages when it reaches the 'develop' branch of the LiquidHaskell repository (or a recent fork). You do **not** need to take any action for this to happen.

If for whatever reason the automatic deployment fails, you can run:

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

## Common Pitfalls

* Markdown files must have extension `.md` (not `.markdown`) to be indexed for tags (current limitation of [the tags plugin](https://github.com/jldiaz/mkdocs-plugin-tags))
* You may need to prefix an extra `../` (or two) to get relative links (e.g. for images) to work OK -- test locally *and* on GH pages
