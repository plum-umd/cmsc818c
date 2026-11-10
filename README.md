# Verified Systems Programming with Proof Agents

Course website and notes for CMSC 818C, written with [Verso](https://github.com/leanprover/verso).
The main course artifact will live in a separate repository; this repository contains the
website, explanatory material, preliminary teaching projects, and PL/OS component assignments.

## Teaching projects

See the [Projects page](https://plum-umd.github.io/cmsc818c/projects/) for assignments and
[projects/](projects/README.md) for the source roadmap.
Each project has an independent Lake package and toolchain. Build projects from their own
directories. The website also checks project examples against the same source files;
the teaching-project workflow checks the standalone package separately in CI.

## Build and preview

Install [elan](https://github.com/leanprover/elan#installation), then run:

```sh
lake build
lake exe generate-blog
python3 -m http.server 8001 --bind 127.0.0.1 --directory _site
```

Open <http://localhost:8001>. The first build downloads the pinned Lean toolchain and
Verso dependencies and may take several minutes. Generated files are ignored by Git.

## Writing notes

The site uses Verso's blog genre, with a home page, an about page, and dated course notes.
Home is available in the top navigation on every page.

- `Blog/FrontPage.lean` is the landing page.
- `Blog/About.lean` introduces the course and its repositories.
- `Blog/Notes.lean` is the grouped table of contents, in suggested reading order.
- `Blog/Posts/` contains individual notes and updates.
- `Blog/Examples/` contains checked worked proofs and regression examples imported by the posts.
- `Blog/Projects.lean` and `Blog/Projects/` contain the project index and assignment descriptions.
- `BlogMain.lean` defines routes, the navigation theme, and the HTML generator.

To add a post, create a file under `Blog/Posts/` following `Welcome.lean`, import it in
`Blog/Notes.lean`, and add it to the `"notes"` section of `courseSite` in `BlogMain.lean`.
Add a link in the appropriate group of the table of contents in `Blog/Notes.lean`.
Mark planned posts as stubs until their content is written.
Give each post a title, author, and date. Verso uses Markdown-like syntax inside
`#doc (Page)` and `#doc (Post)` documents. See the
[Verso manual](https://verso.lean-lang.org/doc/latest/) for authoring details.

After editing, rerun `lake exe generate-blog` and refresh the browser. No commit or push is
needed for local previews.

When the main artifact repository is available, add its link to `Blog/FrontPage.lean` and
`Blog/About.lean`. It is deliberately not a build dependency of this website.

## GitHub Pages

In the repository's **Settings → Pages → Build and deployment**, select **GitHub Actions**
as the source. Push these files to `main` to build and publish the site. Subsequent pushes
to `main` publish automatically; pull requests build the site without deploying it.
The workflow also supports manual runs from the Actions tab.

The expected site URL is <https://plum-umd.github.io/cmsc818c/>.

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the toolchain and dependencies.
When upgrading Verso, choose a matching Lean/Verso release, run `lake update`, and commit the
updated manifest after verifying the build and generated site.
