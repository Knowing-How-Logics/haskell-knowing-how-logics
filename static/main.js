document.addEventListener("DOMContentLoaded", () => {
    const textarea = document.querySelector("textarea");
    const parseBtn = document.querySelector(".main-btn");
    const toggleItems = document.querySelectorAll(".agent-toggle > div");
    const buttonsDiv = document.querySelector(".syntax");

    const singleAgentSyntax = ["P n", "! p", "p & q", "p v q", "p -> q", "KH p q", "T", "( p )"];
    const multiAgentSyntax = ["P n", "! p", "p & q", "p v q", "p -> q", "KH n p q", "( p )"];
    const placeholders = {single: "e.g., KH P12 (P12 & P3 -> P5)", multi: "e.g., KHI 1 P12 !p208"};

    // JS Logic for formula parsing:
    // On load: select single-agent-state
    let selectedState = "single";
    toggleItems[0].classList.add("active");

    // On load: Render syntax and placeholder text
    renderSyntax(singleAgentSyntax);
    textarea.placeholder = placeholders.single;

    // Handle state-toggle clicks
    toggleItems.forEach((item, index) => {
        item.addEventListener("click", () => {
            toggleItems.forEach(i => i.classList.remove("active"));
            item.classList.add("active");
            selectedState = index === 0 ? "single" : "multi";
            renderSyntax(selectedState === "single" ? singleAgentSyntax : multiAgentSyntax);
            textarea.placeholder = placeholders[selectedState];
        });
    });

    // Function to render syntax
    function renderSyntax(syntax) {
        buttonsDiv.innerHTML = ""; // Clear existing buttons
        syntax.forEach(text => {
            const btn = document.createElement("button");
            btn.innerText = text;
            buttonsDiv.appendChild(btn);
        });
    }

    // Disable parse button if textarea empty
    parseBtn.disabled = textarea.value.trim() === "";
    textarea.addEventListener("input", () => {
        parseBtn.disabled = textarea.value.trim() === "";
    });

    // Handle parse button click
    parseBtn.addEventListener("click", async () => {
        try {
            const formula = textarea.value;
            const response = await fetch("/haskell/parse-formula", {
                method: "POST",
                headers: { "Content-Type": "application/x-www-form-urlencoded" },
                body: new URLSearchParams({ formula, state: selectedState })
            });
            const result = await response.text();
            document.querySelector(".output").innerText = result;
        } catch (err) {
            console.error("Error calling Haskell Function:", err);
        }
    });
});