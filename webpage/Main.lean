import VersoBlog

import Site

section
open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <title>"TCSlib — TCS Formalization in Lean 4"</title>
          <link rel="icon" type="image/svg+xml" href="/static/favicon.svg"/>
          <link rel="stylesheet" href="/static/style.css"/>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <nav class="navbar">
              <div class="nav-inner">
                <a class="logo" href="/">"TCSlib"</a>
                <div class="nav-links">
                  <a href="#boolean-analysis">"Boolean Analysis"</a>
                  <a href="#coding-theory">"Coding Theory"</a>
                  <a href="#get-started">"Get Started"</a>
                  <span class="divider">" | "</span>
                  <a href="/blueprint/">"Blueprint"</a>
                  <a href="/docs/">"Docs"</a>
                  <a href="https://github.com/Shilun-Allan-Li/tcslib" aria-label="GitHub" target="_blank">
                    <img src="/static/github.svg" alt="GitHub" width="22" height="22"/>
                  </a>
                </div>
              </div>
            </nav>
          </header>
          <main>
            {{← param "content" }}
          </main>
          <footer>
            <div class="footer-inner">
              <p class="footer-copy">
                "TCSlib · Lean 4 formalization of Theoretical Computer Science · "
                <a href="https://github.com/Shilun-Allan-Li/tcslib">"GitHub"</a>
              </p>
            </div>
          </footer>
        </body>
      </html>
    }}
  }

def tcsSite : Site := site Site.FrontPage /
  static "static" ← "static_files"

def main (args : List String) : IO UInt32 :=
  blogMain theme tcsSite (linkTargets := {}) args
