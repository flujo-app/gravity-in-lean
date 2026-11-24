# Global: status of the team's work on Birkhoff's theorem for a whole space-time

Goals: the seven statements of `Goals/Global.lean`. Times are UTC on 24 November 2026. Lead:
`m0-a0`, started at about 03:05. Working branch: `global`; each item has a branch
`global-<item>` (board claim `task:global-<item>`).

## The seven targets (03:33)

| target | state | file |
|---|---|---|
| `kruskalMapOfSchwarzschild` | proved, merged | `Global/DeSitterNoMap.lean` (halves: `KSOutside.lean`, `KSInside.lean`) |
| `globalDeSitterNoMap` | proved, merged | `Global/DeSitterNoMap.lean` |
| `globalUniqueNeedsOnePiece` | proved, merged | `Global/TwoPieces.lean` |
| `globalBirkhoffConverse` | open: "empty" half proved (`ConverseEmpty.lean`); "round" half given out | `ConverseRoundKruskal.lean`, `ConverseRoundSchw.lean` |
| `globalBirkhoffUnique` | open: chain stated, links given out (see below) | `UniqueFlat.lean`, `UniqueKruskal.lean`, ... |
| `globalMassUnique` | open: needs the curvature scalar links of the chain below | not started |
| `globalBirkhoff` | open: abstract gluing theorem given out (`Develop.lean`) | not started |

None of the three proved targets has been checked in a whole-project build yet; none is in
`GravityInLean.lean` yet. No statement has been reported false.

## The route chosen

Parts 1 and 2 as the supervisor's route. Charts of the model space-times: `SphereSection.lean`
(angles near a direction), `KruskalSection.lean`, `SchwSection.lean` (wrapping can be undone
near every point), `KruskalChart.lean`, `SchwChart.lean` (a length-keeping map is, near each
point, wrapping after a chart of the curved space; so `IsKruskalNear`, `IsSchwarzschildWith`),
`SchwSym.lean` (the symmetries of Schwarzschild's whole space-time keep lengths).

**Part 3 is changed in one place: step 7 (a map is fixed by its value and derivative at one
point, by an ordinary differential equation along lines) is not used.** Instead, at the level
of tables on coordinate space, for a map `f` that keeps Kruskal's table (the change of charts
between two length-keeping maps):

1. `Kretschmann.lean`, `KretschmannKept.lean`, `KretschmannKruskal.lean`: the curvature scalar
   is kept and is a multiple of `m² / r⁶`, so `f` keeps the radius, so it keeps `X² - T²`.
2. `TableHess.lean`, `HessKept.lean`, `HessKruskal.lean`: the second slope of the radius is
   kept; it is `(m / r²) g` on the `(T, X)` plane and `((r - 2m) / r²) g` on the sphere, so `f`
   keeps the split (`KruskalKept.lean`).
3. So `f` is a map of `(T, X)` times a map of the angles. The first keeps `-dT² + dX²`
   (Kruskal's factor `A` depends on the kept radius only), so it is a matrix and a shift
   (`UniqueFlat.lean`'s calculus lemma: a map that keeps a constant form has second derivative
   zero), and the shift is zero because `X² - T²` is kept (`KruskalPlane.lean`).
4. The second keeps the lengths of the unit sphere. Put a time and a distance next to it: a map
   of flat space-time in distance and angles that keeps lengths, so a Lorentz transformation by
   the flat case of uniqueness; it fixes time and distance, so it is a turn or mirror
   (`SphereRigid.lean`).
5. `UniqueKruskal.lean`: so two length-keeping maps differ by a symmetry near every point; the
   symmetry is fixed by what it does near one point; a region in one piece has one symmetry.

The flat case (`UniqueFlat.lean`) is direct: the change of charts keeps a constant form. The
negative mass is planned as the twin of Kruskal's (not stated yet).

Part 5: `Develop.lean` is the abstract statement (pure topology): local maps that exist near
every point, are unique up to a set of symmetries on connected open sets, and whose symmetries
are fixed by an open piece, can be glued to one map on a simply connected, locally path
connected space (covering space of germs; the library's lifting theorem).

## The pieces

| item (`task:global-…`) | file | who | given | built | note |
|---|---|---|---|---|---|
| `ks-outside` | `KSOutside.lean` | m0-a1 | 03:10 | 03:18 | merged |
| `ks-inside` | `KSInside.lean` | m0-a2 | 03:10 | 03:16 | merged |
| `two-pieces` | `TwoPieces.lean` | m0-a4 | 03:10 | 03:17 | merged; target proved |
| `sphere-section` | `SphereSection.lean` | m0-a3 | 03:15 | 03:20 | merged |
| `kruskal-section` | `KruskalSection.lean` | m0-a5 | 03:15 | 03:18 | merged |
| `schw-section` | `SchwSection.lean` | m0-a6 | 03:15 | 03:18 | merged |
| `schw-sym` | `SchwSym.lean` | m0-a7 | 03:15 | 03:19 | merged |
| `kruskal-chart` | `KruskalChart.lean` | m0-a8 | 03:15 | 03:21 | merged |
| `schw-chart` | `SchwChart.lean` | m0-a9 | 03:15 | 03:23 | merged |
| `desitter` | `DeSitterNoMap.lean` | m0-a1 | 03:24 | 03:27 | merged; two targets proved |
| `converse-empty` | `ConverseEmpty.lean` | m0-a2 | 03:24 | 03:28 | merged |
| `converse-round-kruskal` | `ConverseRoundKruskal.lean` | m0-a4 | 03:24 | | |
| `converse-round-schw` | `ConverseRoundSchw.lean` | m0-a5 | 03:24 | | |
| `unique-flat` | `UniqueFlat.lean` | m0-a3 | 03:24 | | |
| `develop` | `Develop.lean` | m0-a6 | 03:24 | | |
| `kretschmann-kept` | `KretschmannKept.lean` | m0-a7 | 03:27 | | |
| `kretschmann-kruskal` | `KretschmannKruskal.lean` | m0-a8 | 03:27 | | |
| `hess-kept` | `HessKept.lean` | m0-a9 | 03:30 | | |
| `hess-kruskal` | `HessKruskal.lean` | m0-a1 | 03:30 | | |
| `sphere-rigid` | `SphereRigid.lean` | m0-a2 | 03:33 | | needs `unique_flat` |
| `kruskal-kept` | `KruskalKept.lean` | | | | stated; needs the four curvature links |
| `kruskal-plane` | `KruskalPlane.lean` | | | | stated |
| `unique-kruskal` | `UniqueKruskal.lean` | | | | stated |
