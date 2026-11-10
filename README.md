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

The RISC assignments depend on the private `plum-umd/plos-risc` repository at a pinned
commit. Local builds of those assignments and the full website require Git read access
to that repository. The six preliminary projects build independently of it.

## GitHub Pages

In the repository's **Settings → Pages → Build and deployment**, select **GitHub Actions**
as the source. Push these files to `main` to build and publish the site. Subsequent pushes
to `main` publish automatically; pull requests build the site without deploying it.
The workflow also supports manual runs from the Actions tab.

The Pages build and RISC-project checks use the repository Actions secret
`PLOS_RISC_READ_TOKEN`: a fine-grained token owned by `plum-umd`, restricted to
`plos-risc` with **Contents: read-only**. Renew the token before its expiration and update
the secret under **Settings → Secrets and variables → Actions**.

The shared `.github/actions/plos-dependency` action validates the three project pins,
checks out that exact private commit with credential persistence disabled, and redirects
Lake's PL/OS Git clones to the local checkout. Credentials are not retained in the checkout
or passed to the Lean build. Private builds disable Actions caching and publish only the generated
website artifact. No dependency source is vendored into this repository.

Fork pull requests run the six public project checks; the website and RISC jobs skip
because fork workflows have no access to the private dependency secret. Pushes and
same-repository pull requests run the full checks. Keep these as `pull_request` workflows,
not `pull_request_target` workflows that execute fork code with repository secrets.

The expected site URL is <https://plum-umd.github.io/cmsc818c/>.

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the toolchain and dependencies.
When upgrading Verso, choose a matching Lean/Verso release, run `lake update`, and commit the
updated manifest after verifying the build and generated site.
