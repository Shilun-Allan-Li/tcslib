---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

{% include mathjax.html %}

# Error Correcting Codes Library

The purpose of this repository is to hold a Lean4 formalization of coding theory, which includes both classical and quantum error correcting codes.

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).
Run `lake exe cache get` and then `lake build` to build the project.

## Build the blueprint

To build the web version of the blueprint, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip install -r blueprint/requirements.txt
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
```
