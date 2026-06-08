# External Data

This directory should contain Kirschmer's `smalltypenumber.m` file, which
defines the Magma list `OneClassGenera`.

The file is not distributed in this repository.  Download it from Markus
Kirschmer's page:

<https://www.math.uni-bielefeld.de/~mkirschm/orders/>

After downloading and unpacking the archive, place the file here:

```text
data/smalltypenumber.m
```

From the repository root, this can be done with:

```sh
curl -L -o /tmp/smalltypenumber.tar.bz2 https://www.math.uni-bielefeld.de/~mkirschm/orders/smalltypenumber.tar.bz2
tar -xjf /tmp/smalltypenumber.tar.bz2 -C data smalltypenumber.m
```

The computational code expects this exact path.  The data file is excluded from
Git by `.gitignore`; this repository only contains the code that consumes the
data.
