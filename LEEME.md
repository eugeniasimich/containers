# Formalización de Containers
Tesina de grado para la obtención del título de Licenciatura en Ciencias de la Computación  
[Departamento de Ciencias de la computación](https://www.fceia.unr.edu.ar/lcc/), [Universidad Nacional de Rosario](http://www.unr.edu.ar/)  
Autora: Eugenia Simich  
Supervisor: [Mauro Jaskelioff](http://www.fceia.unr.edu.ar/~mauro/)  

## Vistazo general del proyecto
La contribución principal del prensente trabajo es una librería de containers en Agda que incluye las formalizaciones de la clausura de la categoría con respecto al producto, coproducto, exponencial y la existencia de objetos terminal e inicial.  
En la carpeta `Category` y archivo `Category.agda` se encuentran las formalizaciones de las nociones categóricas.  
El archivo `Container.agda` y la carpeta `Container` constituyen la librería en sí. Allí se proveen las instancias de cada construcción para el caso de la categoría de containers, así como las demostraciones que garantizan su correctitud.

En la carpeta `doc` se puede encontrar el texto completo de la tesina, compilable realizando `make`. Los paquetes necesarios para una correcta compilación son:

  * Agda v2.5.1 o posterior
  * [Latex](https://www.latex-project.org/get)
  * [babelbib](https://www.ctan.org/pkg/babelbib), paquete latex
  * [catchfilebetweentags](https://www.ctan.org/pkg/catchfilebetweentags), paquete latex



