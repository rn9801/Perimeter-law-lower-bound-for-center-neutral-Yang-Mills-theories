# Manuscript figures

The four `*_audited.pdf` files fill the existing figure references in
`../main.tex`. They are vector drawings; the PNG files are previews.

Regenerate from the manuscript directory with:

```sh
python figures/generate_figures.py
```

The generator requires NumPy and Matplotlib. It draws lattice coordinates
before applying a fixed oblique projection, and checks the half-space
conditions for both diagonal reflections. All endpoint combs have four
unit cells in the long direction. The arrows on red paths indicate path
orientation; combs in the reflection diagrams show the union of their
loop supports, not a new path orientation.

- `comb_audited`: the four based rectangles have lengths 1, 2, 3, and 4,
  width 1, and the orientation prescribed in the Comb Construction
  definition. Red marks each loop's unique far short edge.
- `wilson_line_audited`: both endpoint combs have long direction `+e3`
  and short direction `+e2`, transverse to the red path in direction `e1`.
- `reflection_L_audited`: reflection in `z1=z2` interchanges `e1,e2`
  and preserves `e3`, sending the entire comb at `x` to the comb at `y`.
- `reflection_square_audited`: reflection in `z1+z2=n` fixes `x,y`.
  The reflected combs have short directions `-e1` at `x` and `-e2` at
  `y`. The middle panel orients the square as the concatenation of
  `lambda_n` reversed with its reflection. The last panel chooses
  `r=n=4, s=2`, so `n=max(r,s)` exactly; it illustrates monotonicity,
  not an additional reflection.

The illustrations preserve the supplied manuscript's captions and mathematical
statements.
