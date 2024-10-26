We provide utilities for extracting config JSON files from all Lean projects in [Lean Reservoir](https://reservoir.lean-lang.org/).

## Instructions

1. Go to https://reservoir.lean-lang.org/packages?sort=stars in a browser.
2. Select "500" in the dropdown menu at the bottom to show all projects.
3. Open Developer console, and run the following code:

```js
// Run in Developer console

const leanPackages = [...document.querySelectorAll(".pkg-result")].map(elem => {
    const reservoirTitle = elem.querySelector("a.name").innerText;
    const reservoirURL = elem.querySelector("a.name").href;
    const descriptionElem = elem.querySelector("p > span");
    const description = descriptionElem ? descriptionElem.innerText : null;
    const links = [...elem.querySelectorAll("a.hard-link")];
    const homePageLink = links.find(elem => elem.textContent === "Homepage");
    const homePageURL = homePageLink ? homePageLink.href : null;
    const repositoryURL = links.find(elem => elem.textContent === "Repository").href;
    const stars = Number.parseInt(elem.querySelector("li.stars").innerText);
    const buildSuccess = elem.querySelector(".build-outcome-icon.outcome-success") ? true : false;
    const leanVersionElem = elem.querySelector("span.toolchain");
    const leanVersion = leanVersionElem ? leanVersionElem.innerText : null;

    // hover over the checkmark icon to find the git commit version
    const checkmarkElem = elem.querySelector("span.build-outcome");
    let commitVersion = "";
    if (checkmarkElem) {
        const tooltipElem = checkmarkElem._tippy.popper;
        const tooltipContentElem = tooltipElem.querySelector("span span");
        commitVersion = tooltipContentElem ? /Commit (\w+)/.exec(tooltipContentElem.innerText)[1] : "";
    }

    return {
        reservoirTitle,
        reservoirURL,
        description,
        homePageURL,
        repositoryURL,
        stars,
        buildSuccess,
        leanVersion,
        commitVersion
    }
})

console.log(JSON.stringify(leanPackages));
```

Copy and store the results to `lean_reservoir.json`.

4. Run `python add_package_name_lean_reservoir.py` to add `importName` and `packageName` columns to `lean_reservoir.json` (this is done by fetching lakefile from GitHub).
5. Run `python convert_ntp_toolkit.py` to convert `lean_reservoir.json` to configuration JSONs under `configs/`.
6. Optionally, run `import pandas as pd; pd.read_json("lean_reservoir.json").to_clipboard()` to copy the data to clipboard in spreadsheet form (e.g. to paste to Google Sheets).
