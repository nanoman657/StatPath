# Mapping lane: where Chromium and the spec disagree

| row | spec section | spec says | Chromium does | deviation or open question |
|---|---|---|---|---|
| map_coordinates_test.cc:225 RelposInline, :240 RelposInlineInRelposInline, :210 TextInRelPosInline | CSS 2.1 §9.4.3 relative positioning | a relatively positioned inline box is shifted by `left`/`top` after normal flow, so a point in its local space lies that much further from its container | `LocalToAncestorPoint` of a point from a relatively positioned inline or its text returns the point unchanged (`left:50px; top:100px` maps `(10,10)` to `(10,10)`): the shift is already part of the container-space geometry an inline carries | named rule `Mapping.Node.hop` for `.inline` contributes no offset (law `inline_ignores_rel`); open question whether this is an API convention or a deviation |
