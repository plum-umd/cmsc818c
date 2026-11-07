import VersoBlog
import Blog

open Verso Genre Blog Site Syntax

def courseSite : Site := site Blog.FrontPage /
  "about" Blog.About
  "notes" Blog.Notes with
    Blog.Posts.Welcome

def courseTheme : Theme :=
  { Theme.default with
    primaryTemplate := do
      let page ← Theme.Default.primary
      let navigation ← Theme.topNav (some "Home")
      pure <| page.visitM (m := Id) (tag := fun tag attrs _ =>
        pure <| if tag == "nav" && attrs.contains ("class", "top") then
          some navigation
        else none) }

def main := blogMain courseTheme courseSite
