### Шаблон презентации для докладов

Основной файл --- в demo. Для своей части скопируйте demo в новую директорию.

Собирать как:

* make -C demo --- релиз
* ENGINE=pdflatex mkae -C demo --- через pdflatex, некрасиво, но быстро

Всё остальное --- обвязка. В частности, можете картинки и другой потенциально переиспользуемый матриал компилять в misc/ и вставлять в основной PDF (в demo есть пример). Если всё пихать в один файл --- LaTeX будет долго компилироваться, а это не хорошо.