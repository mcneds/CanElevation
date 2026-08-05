# CanElevation Terrain Exporter

Version 1.0.3

A Tkinter desktop tool for selecting a geographic bounding box on a map and exporting an accurate terrain GeoTIFF from Natural Resources Canada's CanElevation STAC collections.

## Outputs

- Float32 GeoTIFF elevation master, in the source collection's metric CRS
- JSON metadata containing the selected WGS84 box, source collection, source items, resolution, elevation range, and nodata value
- Optional normalized 16-bit heightmap preview PNG
- Optional hillshade preview PNG

The GeoTIFF is the accurate master. The preview PNG is normalized to the exported area's minimum and maximum elevation and is intended for visualization, not as the sole archival dataset.

## Windows

1. Install 64-bit Python 3.12 or newer from python.org. During installation, enable **Add Python to PATH**.
2. Double-click `run_windows.bat`.
3. The first launch creates a local `.venv` and installs the required packages.

## Linux

Tkinter may need to be installed by the system package manager first. On Ubuntu/Debian:

```bash
sudo apt install python3-tk python3-venv
```

Then run:

```bash
./run_linux.sh
```

## Use

1. Pan and zoom the map.
2. Press **Draw box — click 2 corners**, then click opposite corners of the desired area; or enter west/south/east/north coordinates manually.
3. Press **Inspect coverage for this box** to see which CanElevation collection actually has valid DTM coverage.
4. Leave the dataset on **Auto** to select the highest-resolution dataset with at least 99.5% estimated valid coverage.
5. Choose an output folder and filename, then press **Export selected terrain**.
6. Open **Show log** for detailed progress and source-item information.

## Notes

- The program reads only the selected windows from remote Cloud Optimized GeoTIFFs rather than downloading whole source tiles.
- Large 1 m exports can still require substantial time, disk space, and network transfer.
- Export cancellation occurs after the current raster block finishes.
- HRDEM elevation heights are referenced to CGVD2013 according to NRCan collection metadata.

