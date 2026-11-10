import Widgets.Sweep
import Widgets.TriangularBatch
import Widgets.FrozenLock
import Widgets.NetCalc

/-!
# Widgets — banked-road min-plus/SSSP widgets

Importable lemma family for the min-plus/SSSP lanes:

* `Widgets.Sweep` — the discrete min-plus sweep engine (values decrease,
  improving edges unlock heads, fixpoint = Bellman system).
* `Widgets.TriangularBatch` — one-batch-pass settle license for
  triangular (topologically ordered) min-plus systems (Luo–Zhao 2016).
* `Widgets.FrozenLock` — frozen-lock exclusion + potential-bounded
  termination (Zhao 2005).
* `Widgets.NetCalc` — discrete min-plus network calculus: convolution
  algebra, closure, service curve ⇒ delay bound.

Consumers: FT `sssp-nlogn` (`machinePotential` rows), `apsp-l1-work`
(triangular product-round body, segment assembly), `subset-sum-bridge`
(ladder Bound-arithmetic).
-/
