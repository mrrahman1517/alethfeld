# Quick Fix for Clojure Build Issue

## Problem

The error you're seeing:
```
Execution error (FileNotFoundException) at java.io.FileInputStream/open0 (FileInputStream.java:-2).
-T:build (No such file or directory)
```

This happens because the system `clojure` package is the **old REPL version**, not the **Clojure CLI Tools** that Alethfeld needs.

## Solution

Install Clojure CLI Tools using the official installer:

```bash
# Download installer
curl -O https://download.clojure.org/install/linux-install-1.11.1.1347.sh
chmod +x linux-install-1.11.1.1347.sh
sudo ./linux-install-1.11.1.1347.sh

# Add to PATH
export PATH="$HOME/.clojure/bin:$PATH"

# Verify it works
clj --version
clojure -Spath

# Now build Alethfeld
cd /home/muntasir/Assembly/alethfeld/cli
clojure -T:build uber
```

## Alternative: Use SDKMAN

```bash
# Install SDKMAN
curl -s "https://get.sdkman.io" | bash
source "$HOME/.sdkman/bin/sdkman-init.sh"

# Install Clojure
sdk install clojure

# Build Alethfeld
cd /home/muntasir/Assembly/alethfeld/cli
clojure -T:build uber
```

## What's the Difference?

- **Old `clojure` command**: REPL-based, doesn't support `-T` tooling flag
- **Clojure CLI Tools (`clj`)**: Modern tooling with `-T` for build tools, `-M` for main, etc.

Alethfeld's build system uses `-T:build uber` which requires the CLI Tools version.

## If You Can't Install CLI Tools

You can still use the LaTeX file directly without building the CLI:

```bash
cd examples/sum-degrees-even
pdflatex sum-degrees-even.tex
```

The CLI tools are only needed for:
- Validating EDN files
- Viewing statistics
- Manipulating proof graphs

The LaTeX compilation works independently.
