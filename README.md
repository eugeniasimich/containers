# Construyendo tipos de datos con containers

## Abstract  
Muchos de los tipos de datos más utilizados comparten la característica de poder ser pensados como una serie de esqueletos, o plantillas, para contener otros datos. Las listas, los árboles, los streams, son ejemplos de tipos de datos de esta clase. Esta propiedad que los integra permite analizarlos de forma segregada: por una lado se encuentra su estructura y por otro la información a almacenar. Los containers se presentan como una buena alternativa de representación de esta clase de constructores de tipos, explotando esta potencialidad de separar estructura de contenido y proveyendo la posibilidad de estudiar la estructura de forma aislada.

En esta charla introduciré a los containers como una forma alternativa de describir constructores de tipos de datos, a partir de ejemplos en lenguaje de programación Agda. Mostraré su utilidad a la hora de programar genéricamente.

## Fuente de las slides  
Compilables haciendo `make`. Se necesita:

  * Agda v2.5.1 or later
  * [Latex](https://www.latex-project.org/get/)
  * [babelbib](https://www.ctan.org/pkg/babelbib) latex package
  * [catchfilebetweentags](https://www.ctan.org/pkg/catchfilebetweentags) latex package

Para indicar al Makefile la ubicación de la librería estándar de Agda, simplemente copiar el archivo `agda_stdlib.mk.example` en uno nuevo `agda_stdlib.mk`, completando correctamente la ruta al directorio.
