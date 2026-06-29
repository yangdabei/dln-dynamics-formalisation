"""Single source of truth for the therisensea.org tab nav.

Every page producer (tide-mirror's section indices, tide-digest's home/Seabeds
index) renders its `<nav class="tabs">` from `render_nav` here, rather than
hardcoding the tab list in its own page template. This is the structural fix for
the nav-clobber class of bug: when each generator carried its own copy of the
tab list, adding a tab (e.g. Reviews) to one generator's template silently left
the others to overwrite it on their next run. With one definition, a full-page
regeneration is *safe* — it regenerates the canonical nav — and adding a future
tab is a one-line edit to `TABS` below.

Add a tab: append `(label, href)` to `TABS`. Both generators pick it up.
"""

# Canonical, ordered tab list for the whole site. (label, href)
TABS: list[tuple[str, str]] = [
    ("Seabeds", "/"),
    ("Experiments", "/experiments/"),
    ("Tides", "/tides/"),
    ("Reviews", "/reviews/"),
    ("Today", "/today/"),
]


def render_nav(active_href: str, *, indent: str = "    ") -> str:
    """Return the `<nav class="tabs">` block, with the tab whose href equals
    ``active_href`` marked ``tab-active``.

    ``indent`` is the leading whitespace for the opening ``<nav>`` tag (the
    ``<a>`` children are indented two spaces deeper), so the output drops into
    the existing templates at their current indentation.
    """
    lines = [f'{indent}<nav class="tabs">']
    for label, href in TABS:
        cls = "tab tab-active" if href == active_href else "tab"
        lines.append(f'{indent}  <a href="{href}" class="{cls}">{label}</a>')
    lines.append(f"{indent}</nav>")
    return "\n".join(lines)
