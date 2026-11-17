# Paper

[main.pdf](main.pdf) is the compiled paper, **Perimeter law lower bound for
center-neutral Yang–Mills theories**. Its LaTeX source is [main.tex](main.tex).
The bibliography, style files, supplementary reflection-positivity source,
and [figures](figures/README.md) are kept alongside it.

To rebuild with a TeX Live installation containing the packages used in
`sky.sty` (including Mathabx, Boondox and BBM), run from this folder:

```sh
mkdir -p /tmp/gluelump-paper-build
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/gluelump-paper-build main.tex
cp /tmp/gluelump-paper-build/main.pdf main.pdf
```

This keeps the compiled PDF beside the source and auxiliary build files in
`/tmp/gluelump-paper-build`.
