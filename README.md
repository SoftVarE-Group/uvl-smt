# UVL-SMT: A JavaSMT-Based Reasoning Library for UVL

### Dependencies

This project depends on [JavaSMT](https://github.com/sosy-lab/java-smt) for reasoning and [java-fm-metamodel](https://github.com/Universal-Variability-Language/java-fm-metamodel/tree/refactoring_metamodel) for the internal feature model representation.
The required dependencies are part of the pom.xml and can be installed via maven.
To use Z3, we need the binaries in `src/main/resources/bin`. They can be included by setting `-Djava.library.path=./src/main/resources/bin`

The compilation can be performed using maven, e.g., `mvn clean compile`

### Usage 

Example for checking satisfiability of a UVL feature model:
```java
FMToSmtConverter smtConverter;
try {
    smtConverter = new FmToSMTConverter(uvlFeatureModel);
} catch (InvalidConfigurationException e) {
    throw new RuntimeException(e);
}
smtChecker = new SMTSatisfiabilityChecker(smtConverter.convertFeatureModel(), smtConverter.getContext());
smtChecker.isSat();
```