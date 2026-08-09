# Phase 75.12.9 — GeneralFourBlock extensionality fix

Adds a registered `[ext]` theorem for `HC4.Newton.GeneralFourBlock`.

This fixes the two failures in `HC4.Valuation.RigidPacketZeroSchurBridge` where
Lean reported that no applicable extensionality theorem was registered for
`GeneralFourBlock K`.

No theorem statements or mathematical assumptions in the bridge are changed.
