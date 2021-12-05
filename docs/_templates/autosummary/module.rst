{{ objname }}
{{ underline }}


.. automodule:: {{ fullname }}
    :members:

    .. autosummary::
        {% for x in functions %}
            {{ x }}
        {% endfor %}
