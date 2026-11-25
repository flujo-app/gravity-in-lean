# The pages

The interactive pages this project grew out of. Each one is a single file.

To look at one: open its link below, or start from the front page,
[flujo-app.github.io/gravity-in-lean](https://flujo-app.github.io/gravity-in-lean/). Or download
the file and open it in a browser. Either way it needs the internet, because it loads its 3D
library and its fonts from the web.

| Page | What it is | File | Online |
|---|---|---|---|
| **Slow Clocks, Bent Light** | Real space around a heavy mass, with a light mass, a far observer, a flashing light source and your ship. One row per clock runs along the top. Fly around, switch whose clock you follow, watch light bend and clocks slow. The formulas checked in this repository come from this page. | [slow-clocks-bent-light.html](slow-clocks-bent-light.html) | [open](https://flujo-app.github.io/gravity-in-lean/slow-clocks-bent-light.html) |
| **Everything Rises** | Sideways is space, up is the time each thing has lived. Everything climbs. Moving tilts your climb, and a heavy thing makes a funnel. | [everything-rises.html](everything-rises.html) | [open](https://flujo-app.github.io/gravity-in-lean/everything-rises.html) |
| **Slow Light Town** | A town where light moves at walking pace, so far streets are in the past and running bends what you see. | [slow-light-town.html](slow-light-town.html) | [open](https://flujo-app.github.io/gravity-in-lean/slow-light-town.html) |
| **Slices of Time** | A block of space-time cut in four ways: at rest, moving, falling, and falling along. | [slices-of-time.html](slices-of-time.html) | [open](https://flujo-app.github.io/gravity-in-lean/slices-of-time.html) |
| **The Dome and the Horn** | Two curved pictures of the motion budget: a dome without gravity, a horn with it. | [dome-and-horn.html](dome-and-horn.html) | [open](https://flujo-app.github.io/gravity-in-lean/dome-and-horn.html) |
| **Light Clock &amp; Falling Wave** | A light clock that shows why moving clocks run slow, and a matter wave that falls. | [light-clock-falling-wave.html](light-clock-falling-wave.html) | [open](https://flujo-app.github.io/gravity-in-lean/light-clock-falling-wave.html) |
| **Spacetime Speedometer** | The motion budget as a dial: what you spend on moving through space is missing from your moving through time. | [spacetime-speedometer.html](spacetime-speedometer.html) | [open](https://flujo-app.github.io/gravity-in-lean/spacetime-speedometer.html) |
| **Arrows to Amplitudes** | Six short chapters on the maths behind quantum physics: arrows, adding, stretching, matrices, arrows that cancel to make the double-slit stripes, and paths and clocks, where every path of a thrown ball gets an arrow that its own clock turns and only the paths near the one with the most clock time survive. Each chapter asks questions you answer before you check. | [arrows-to-amplitudes.html](arrows-to-amplitudes.html) | [open](https://flujo-app.github.io/gravity-in-lean/arrows-to-amplitudes.html) |
| **Turns and a Mirror** | One picture of a quarter turn, a half turn and a mirror, with a letter F so you can see which way things face. | [turns-explainer.svg](turns-explainer.svg) | [open](https://flujo-app.github.io/gravity-in-lean/turns-explainer.svg) |

## Good to know

- **Start with the first one.** The next six are the earlier tries that led to it, kept because
  each shows the same idea from a different side.
- **The last two are a separate maths lesson.** Arrows to Amplitudes teaches vectors and
  matrices from zero, as a first step towards quantum physics. The turns picture is a plain image
  that goes with its matrices chapter, first shown in a chat. Neither is part of
  the gravity work, except that the lesson's last chapter, paths and clocks, is where the two
  meet: the clock it uses is the same slow-clock rule as the gravity pages. The lesson was tested
  in a browser (dragging, sliders, answer checks, phone layout, light and dark). Its double-slit
  pattern is a simple model that shows the idea, not real measurements. Its paths chapter uses
  smooth arcs only, made-up units, and weak gravity; the best arc it finds is the real flight of a
  thrown ball.
- **How sure is this?** The first page was tested with numbers against the textbook formulas, and
  several of its formulas are now proved by machine in this repository (see the main README).
  The earlier pages are pictures: good for the idea, not tested the same way.
- **What these files are.** Each file is the page exactly as it was first published (as a page
  on claude.ai), wrapped in a few lines so that it opens by itself. The site shows these same
  files, unchanged: the workflow `.github/workflows/pages.yml` copies this folder to it whenever
  something here changes. Its front page is `index.html`; `preview.jpg` and `hero.jpg` are
  screenshots of the first page, with and without its controls.
