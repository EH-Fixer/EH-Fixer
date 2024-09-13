# EH-Fixer
Error Delayed is Not Error Handled: Understanding and Fixing Propagated Error-Handling Bug

---

## Introduction
Error handling may be delayed to other functions. Such propagated error handling (PEH) could easily be missed and lead to bugs. Our research reveals that PEH bugs are prevalent in software systems and, on average, take 42.3 days to fully address. Existing approaches have primarily focused on the error-handling bug within individual functions, which makes it difficult to fully address PEH bugs. EH-Fixer is an LLM-based APR approach for PEH bugs. it guides LLMs to trace the error propagation path and fix PEH bugs based on a retrieval augmented technique.

## Usage

### Dependency

- Tree-sitter 0.20.0
- Prefixspan 0.5.2
- numpy 1.12.1

### Envirment Setup

- Download grammars for tree-sitter.

```
git clone https://github.com/tree-sitter/tree-sitter-c
git clone https://github.com/tree-sitter/tree-sitter-cpp
```

- Add the paths to these grammars to TreesitterInit.

```
Language.build_library(
  # Store the library in the `build` directory
  'build/my-languages.so',
  # Include one or more languages
  [
  Path1,
  Path2
  ]
)
```

- Run TreesitterInit.py.

```
sudo ./TreesitterInit.py
```

- EH-Digger requires the project to be structured as follow.

```
Working Dir
|
|----Test
|        |----project1
|        |----project2
|
|----TestResult
|        |----result1
|        |----return2
```

- Add the path of the Working Dir to Config.

```
workingDir = Working Dir
```

- Add the project name and corresponding error log patterns.

```
pInfoList = [[ProjectName, [Error Log Pattern],[Error Log Pattern],...]]
bugLocation = [[filePath, lineNumber]]
```

### Run EH-Fixer

```
sudo ./run.py
```

### Check Result

```
cat Working Dir/TestResult/ProjectName/Result.txt
```
