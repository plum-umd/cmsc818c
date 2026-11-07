# Verified Systems Programming with Proof Agents

Course website and notes for CMSC 818C, written with [Verso](https://github.com/leanprover/verso).
The main course artifact will live in a separate repository; this repository contains the
website and explanatory material.

## Build and preview

Install [elan](https://github.com/leanprover/elan#installation), then run:

```sh
lake build
lake exe generate-book --depth 2
python3 -m http.server 8000 --directory _out/html-multi
```

Open <http://localhost:8000>. The first build downloads the pinned Lean toolchain and
Verso dependencies and may take several minutes. Generated files are ignored by Git.

## Writing notes

- `Book.lean` is the landing page and chapter list.
- `Book/Introduction.lean` introduces the course and its repositories.
- `Book/Notes.lean` is the starting point for course notes.
- `Main.lean` runs Verso's HTML generator.

To add a chapter, create a file under `Book/` following an existing chapter, import it in
`Book.lean`, and add `{include 1 Book.YourChapter}` at the desired position. Verso uses
Markdown-like syntax inside `#doc (Manual)` documents. See the
[Verso manual](https://verso.lean-lang.org/doc/latest/) for authoring details.

When the main artifact repository is available, add its link to `Book.lean` and
`Book/Introduction.lean`. It is deliberately not a build dependency of this website.

## GitHub Pages

In the repository's **Settings → Pages → Build and deployment**, select **GitHub Actions**
as the source. Push these files to `main` to build and publish the site. Subsequent pushes
to `main` publish automatically; pull requests build the site without deploying it.
The workflow also supports manual runs from the Actions tab.

The expected site URL is <https://plum-umd.github.io/cmsc818c/>.

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the toolchain and dependencies.
When upgrading Verso, choose a matching Lean/Verso release, run `lake update`, and commit the
updated manifest after verifying the build and generated site.
