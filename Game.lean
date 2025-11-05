import Game.Levels.MonoidWorld

-- Here's what we'll put on the title screen
Title "Abstract Algebra Game"
Introduction
"
Welcome to *Abstract Algebra Game*. This is a theorem proving game similar to Natural
Number Game. It is a way to learn mathematics and lean4 in a very interactive way,
similar to playing a computer game. Although, in *Abstract Algebra Game* we focus more
on mathlib-style mathematics. The player is expected to have basic familiarity with
theoram proving by playing games about Logic and Set (insert link here). Knowledge of
abstract mathematics is helpful but not required

### The material
This is an interactive way to learn abstract algebra in lean. It is expected to be
hands-on first approach where the user is proving thoerem, and when they are stuck
there is always Hints on the left side panel to help them. Also they can click on the
defintions and theorems on the right-side panel to gets more inforamtion.

"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use **markdown**.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
