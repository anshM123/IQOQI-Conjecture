# Figures of the article

`make_figures.py` computes the explicit symmetrically thermalizing unitaries from the construction of the proof,
using the interval uniformisations implemented in `../checks/check_constructions_lib.py`, and produces
`figures/fig1.pdf`, `fig2.pdf` and `fig3.pdf`. It also prints the numbers quoted in the figure captions; the
output of our run is in `make_figures.log`.

Requirements: Python 3 with numpy, matplotlib and mpmath.

```bash
python make_figures.py
```
