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
          <link rel="icon" type="image/svg+xml" href="/tcslib/static/favicon.svg"/>
          <link rel="icon" type="image/png" sizes="96x96" href="/tcslib/static/favicon-96x96.png"/>
          <link rel="shortcut icon" href="/tcslib/static/favicon.ico"/>
          <link rel="apple-touch-icon" sizes="180x180" href="/tcslib/static/apple-touch-icon.png"/>
          <link rel="manifest" href="/tcslib/static/site.webmanifest"/>
          <link rel="stylesheet" href="/tcslib/static/style.css"/>
          <script src="/tcslib/static/theme.js">""</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <nav class="navbar">
              <div class="nav-inner">
                <a class="logo" href="/tcslib/">"TCSlib"</a>
                <div class="nav-links">
                  <a href="#boolean-analysis">"Boolean Analysis"</a>
                  <a href="#coding-theory">"Error-Correcting Codes"</a>
                  <a href="#get-started">"Get Started"</a>
                  <span class="divider">" | "</span>
                  <a href="/tcslib/blueprint/">"Blueprint"</a>
                  <a href="/tcslib/docs/">"Docs"</a>
                  <span class="divider">" | "</span>
                  <div class="nav-icons">
                    <button id="theme-toggle" class="theme-toggle" aria-label="Toggle theme">
                      <img id="theme-icon" src="/tcslib/static/moon.svg" alt="" width="22" height="22"/>
                    </button>
                    <a href="https://github.com/Shilun-Allan-Li/tcslib" aria-label="GitHub" target="_blank">
                      <img src="/tcslib/static/github.svg" alt="GitHub" width="22" height="22"/>
                    </a>
                  </div>
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
