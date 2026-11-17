# Perimeter law manuscript

`main.tex` is the supplied manuscript; `main.pdf` is its compiled version
with all four figures. The text and captions are unchanged.

The illustrations are vector PDFs in `figures/`, accompanied by PNG
previews and a reproducible Python generator. See [figure notes](figures/README.md)
for the geometry represented in each panel.

Build from this directory with a TeX Live installation containing the
packages used in `sky.sty` (including Mathabx, Boondox and BBM):

```sh
mkdir -p /tmp/gluelump-paper-build
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/gluelump-paper-build main.tex
```

The output is `/tmp/gluelump-paper-build/main.pdf`. Auxiliary files stay
outside the source directory.
