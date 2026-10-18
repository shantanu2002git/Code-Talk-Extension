# Code-Talk-Extension
 # Code Talk

**Understand code by watching it execute, step by step.**

Code Talk is a Chrome extension designed to help developers and coding learners understand Data Structures and Algorithms (DSA) through interactive code execution and visualization.

Instead of only reading a solution, you can follow its execution, inspect variable changes, explore data structures, and investigate errors directly in your browser.

## ✨ Features

- **Step-by-Step Execution:** Move through your code one step at a time.
- **Multi-Language Tracing:** Supports C++, Java, and Python within the supported language features.
- **Automatic Code Detection:** Attempts to extract problem details and code from LeetCode and GeeksforGeeks.
- **Variable Tracking:** Understand how variable values change during execution.
- **Data Structure Visualization:** Explore arrays, linked lists, trees, graphs, and other supported structures.
- **Interactive Controls:** Play, pause, move forward or backward, reset, and adjust playback speed.
- **Debugging Insights:** Inspect runtime errors and receive helpful explanations.
- **Complexity Analysis:** Analyze time and space complexity where supported.
- **Reference Solutions:** Access bundled solutions for selected coding problems.

## 🎯 Why Code Talk?

Understanding how an algorithm works can be harder than writing the code itself. Code Talk helps bridge that gap by turning execution into a visual learning experience.

Whether you're learning loops, recursion, linked lists, trees, or other DSA concepts, Code Talk helps you explore what happens inside your program.

## 🛠️ Technology Stack

- JavaScript (ES Modules)
- HTML and CSS
- Chrome Extension Manifest V3
- Custom C++/Java tracing interpreter
- Python with Pyodide and WebAssembly
- Web Workers

## 🚀 Installation

1. Download or clone this repository.
2. Open `chrome://extensions/` in Google Chrome.
3. Enable **Developer mode**.
4. Click **Load unpacked**.
5. Select the repository folder containing `manifest.json`.
6. Open a supported LeetCode or GeeksforGeeks problem.
7. Click the Code Talk extension icon to open the side panel.

## 📚 Supported Platforms

- LeetCode
- GeeksforGeeks

Language support depends on the interpreter's implemented features. Reference solutions are available only for selected problems and languages.


