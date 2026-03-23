document.addEventListener("DOMContentLoaded", () => {
    console.log("DOM loaded");

    const textarea = document.querySelector("textarea");
    const parseFormBtn = document.querySelector("#parse-formula-btn");
    const parseModelBtn = document.querySelector("#parse-model-btn");
    const modelInputs = document.querySelectorAll(".model-input");
    

    const generateFormulaBtn = document.querySelector("#random-formula-btn");
    const generateModelBtn = document.querySelector("#random-model-btn");
    const toggleItems = document.querySelectorAll(".agent-toggle > div");
    const buttonsDiv = document.querySelector(".syntax");

    const singleAgentSyntax = ["P n", "! p", "p & q", "p v q", "p -> q", "KH p q", "T", "( p )"];
    const multiAgentSyntax = ["P n", "! p", "p & q", "p v q", "p -> q", "KH n p q", "( p )"];
    const placeholders = { single: "e.g., KH P12 (P12 & P3 -> P5)", multi: "e.g., KHI 1 P12 !p208" };

    // JS Logic for formula parsing:
    // On load: select single-agent-language
    let selectedLanguage = "single";
    toggleItems[0].classList.add("active");

    // On load: Render syntax and placeholder text
    renderSyntax(singleAgentSyntax);
    textarea.placeholder = placeholders.single;

    // Handle language-toggle clicks
    toggleItems.forEach((item, index) => {
        item.addEventListener("click", () => {
            toggleItems.forEach(i => i.classList.remove("active"));
            item.classList.add("active");
            selectedLanguage = index === 0 ? "single" : "multi";

            renderSyntax(selectedLanguage === "single" ? singleAgentSyntax : multiAgentSyntax);
            textarea.placeholder = placeholders[selectedLanguage];

            generateFormulaBtn.disabled = selectedLanguage === "multi"
            generateModelBtn.disabled = selectedLanguage === "multi"
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
    parseFormBtn.disabled = textarea.value.trim() === "";
    textarea.addEventListener("input", () => {
        parseFormBtn.disabled = textarea.value.trim() === "";
    });

    function validateModelInputs() {
        const allFilled = Array.from(modelInputs).every(input => input.value.trim() !== "");
        parseModelBtn.disabled = !allFilled;
    }

    // Initial state (disabled if empty)
    validateModelInputs();

    // Listen for changes
    modelInputs.forEach(input => {
        input.addEventListener("input", validateModelInputs);
    });


    // Haskell calls:
    parseFormBtn.addEventListener("click", async () => {
        try {
            const formula = textarea.value;
            const response = await fetch("/parse-formula", {
                method: "POST",
                headers: { "Content-Type": "application/x-www-form-urlencoded" },
                body: new URLSearchParams({ formula, language: selectedLanguage })
            });
            const result = await response.text();
            document.querySelector("#formula-output").innerText = result;
        } catch (err) {
            console.error("Error parsing formula:", err);
        }
    });

    parseModelBtn.addEventListener("click", async () => {
    try {
        const inputs = document.querySelectorAll(".model-input");

        const states = inputs[0].value;
        const actions = inputs[1].value;
        const props = inputs[2].value;
        const agents = inputs[3].value;

        const response = await fetch("/parse-model", {
            method: "POST",
            headers: { "Content-Type": "application/x-www-form-urlencoded" },
            body: new URLSearchParams({
                states,
                actions,
                props,
                agents,
                language: selectedLanguage
            })
        });

        const result = await response.text();
        document.querySelector("#model-output").innerText = result;

    } catch (err) {
        console.error("Error generating model:", err);
    }
});

    generateFormulaBtn.addEventListener("click", async () => {
        try {
            const response = await fetch("/random-formula");
            const result = await response.text();
            document.querySelector("#formula-output").innerText = result;
        } catch (err) {
            console.error("Error generating random formula:", err);
        }
    })

    generateModelBtn.addEventListener("click", async () => {
        try {
            const response = await fetch("/random-model");
            const result = await response.text();
            document.querySelector("#model-output").innerText = result;
        } catch (err) {
            console.error("Error generating random model:", err);
        }
    })
});