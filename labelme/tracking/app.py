# -*- coding: utf-8 -*-

"""
-----------------------------
 Ver    Date     Who    Descr
-----------------------------
2327   05.08.24 UD     Icon with L. Printing error in JSON
2326   19.02.24 UD     Selecting path once.
2317   08.04.22 UD     Points outside the image are OK
2316   17.03.22 BM     Exports to the same folder
2315   30.11.21 BM     Automatically projects points, other small bug fixes
2313   25.10.21 BM     Added extracting frames options
2312   11.10.21 BM     Clears projected shape easier, fixes tracking bug
2310   22.09.21 BM     Axis shows on image, get rid of unnecessary code in compute shapes function
2309   20.09.21 BM     Fixed error when jsonfile is None, fixed axis size, shapes appear on picture, copy json files into new folder, 
                        fixed license version
2308   29.08.21 BM     Fixed edit modes and create modes, upload json file before starting, fixed location of session file, 
                        exports all objects even if number is out of order, doesn't ask before deleting point, select multiple objects,
                        show shape for all objects
2307   11.08.21 BM     Ensure Ascii is true for json files
2306   01.08.21 BM     Fixed bug with Axis Projection, created license for export files
2305   26.07.21 BM     Got rid of Config Manager application, project points uses only object_params
2304   21.07.21 BM     Changed Label completion to min of 5 points, increased tracker size to 64, auto save updated in session file
2303   12.07.21 BM     Added lastopendir and lastopenimg to session file
2302   06.07.21 BM     Added axis button
2301   29.06.21 BM     Export Files
2300   22.06.21 BM     Changed Json file format, for projectedShapes
2205   17.06.21 BM     Added Shape projection, smaller font size
2204   15.06.21 BM     Fix bug with png files, fixed projectedImageWindow, renamed labelmerc to label6d_config
2203   31.05.21 BM     Added to help menu, fixed labelmerc location
-----------------------------
"""

import functools
import json
import math
import os
import os.path as osp
import yaml
import sys
# here = osp.dirname(osp.abspath(__file__))
# ffmpeg_dir = osp.join(here, "ffmpeg/ffmpeg.exe")
# os.environ["IMAGEIO_FFMPEG_EXE"] = ffmpeg_dir

import re
import webbrowser
import imageio
import tqdm
import shutil
import pylab as m

import numpy as np
import imgviz
from qtpy import QtCore
from qtpy.QtCore import Qt
from qtpy import QtGui
from qtpy import QtWidgets

from gui import __appname__
from gui import __version__
from gui import PY2
from gui import QT5

import utils
from config import get_config, resource_path
from gui.label_file import LabelFile
from gui.label_file import LabelFileError
from gui.logger import logger
from gui.shape import Shape
from license.LicenseManager import LicenseManager
from transform.LabelManager import LabelManager
from transform.ConfigManager import ConfigManager
from widgets import BrightnessContrastDialog
from widgets import Canvas
from widgets import LabelDialog
from widgets import LabelListWidget
from widgets import LabelListWidgetItem
from widgets import projectedImage
from widgets import projectedShape
from widgets import projectedAxis
from widgets import ToolBar
from widgets import UniqueLabelQListWidget
from widgets import ZoomWidget
from point_tracking import ObjectDetector
from utils.frame_extraction import extract_frames 


# FIXME
# - [medium] Set max zoom value to something big enough for FitWidth/Window

# TODO(unknown):
# - Combine show shapes and show labels
# - Add button to export all files at once
# - [high] Add polygon movement with arrow keys
# - [high] Deselect shape when clicking and already selected(?)
# - [low,maybe] Preview images on file dialogs.
# - Zoom is too "steppy".
# - Change every open file dialog to start in last open dir
# - open last img/dir right away


LABEL_COLORMAP = imgviz.label_colormap(value=200)
isDeployed = False
if hasattr(sys, 'frozen') and hasattr(sys, '_MEIPASS'):
    isDeployed = True
    base_path = sys._MEIPASS
else:
    base_path = os.path.abspath(".")

# clean files that are left from killing the app
temp_path, current_folder = os.path.split(base_path)
print('Removal of Temp Files in progress')
for dir_to_remove in os.listdir(temp_path):
    dir_full_name = os.path.join(temp_path,dir_to_remove)
    if os.path.isdir(dir_full_name) and dir_to_remove.startswith("_MEI"):
        if dir_to_remove != current_folder:
            print('Cleaning up the mess %s' %dir_to_remove)
            try:
                shutil.rmtree(dir_full_name)
            except:
                print('Failed to delete %s' %dir_to_remove)

class MainWindow(QtWidgets.QMainWindow):
    FIT_WINDOW, FIT_WIDTH, MANUAL_ZOOM = 0, 1, 2

    def __init__(
            self,
            config=None,
            filename=None,
            output=None,
            output_file=None,
            output_dir=None,
    ):
        if output is not None:
            logger.warning(
                "argument output is deprecated, use output_file instead"
            )
            if output_file is None:
                output_file = output

        # see labelme/config/default_config.yaml for valid configuration
        if config is None:
            config = get_config()
        self._config = config
        config_shape = self._config.get("shape")

        # set default shape colors
        Shape.line_color = QtGui.QColor(*config_shape.get("line_color"))
        Shape.fill_color = QtGui.QColor(*config_shape.get("fill_color"))
        Shape.select_line_color = QtGui.QColor(
            *config_shape.get("select_line_color")
        )
        Shape.select_fill_color = QtGui.QColor(
            *config_shape.get("select_fill_color")
        )
        Shape.vertex_fill_color = QtGui.QColor(
            *config_shape.get("vertex_fill_color")
        )
        Shape.hvertex_fill_color = QtGui.QColor(
            *config_shape.get("hvertex_fill_color")
        )
        Shape.select_line_width = config_shape.get("select_line_width")

        super(MainWindow, self).__init__()
        self.setWindowTitle(__appname__)

        # Whether we need to save or not.
        self.dirty = False

        self._noSelectionSlot = False

        # Main widgets and related state.
        self.labelDialog = LabelDialog(
            parent=self,
            labels=self._config.get("labels"),
            sort_labels=self._config.get("sort_labels"),
            show_text_field=self._config.get("show_label_text_field"),
            completion=self._config.get("label_completion"),
            fit_to_content=self._config.get("fit_to_content"),
            flags=self._config.get("label_flags"),
        )

        self.labelList = LabelListWidget()
        self.lastOpenDir = self._config.get("last_open_dir")
        self.lastJsonDir = self._config.get("last_open_dir")
        self.flag_dock = self.flag_widget = None
        self.flag_dock = QtWidgets.QDockWidget(self.tr("Flags"), self)
        self.flag_dock.setObjectName("Flags")
        self.flag_widget = QtWidgets.QListWidget()
        if self._config.get("flags"):
            self.loadFlags({k: False for k in self._config.get("flags")})
        self.flag_dock.setWidget(self.flag_widget)
        self.flag_widget.itemChanged.connect(self.setDirty)

        self.labelList.itemSelectionChanged.connect(self.labelSelectionChanged)
        self.labelList.itemDoubleClicked.connect(self.setEditMode)
        self.labelList.itemChanged.connect(self.labelItemChanged)
        self.labelList.itemDropped.connect(self.labelOrderChanged)
        self.shape_dock = QtWidgets.QDockWidget(
            self.tr("Point Labels"), self
        )
        self.shape_dock.setObjectName("Labels")
        self.shape_dock.setWidget(self.labelList)

        self.uniqLabelList = UniqueLabelQListWidget()
        self.uniqLabelList.itemDoubleClicked.connect(self.setCreateMode)
        self.uniqLabelList.setToolTip(
            self.tr(
                "Select label to start annotating for it. "
                "Press 'Esc' to deselect."
            )
        )
        self.objectList = UniqueLabelQListWidget()
        self.objectList.setSelectionMode(QtWidgets.QAbstractItemView.ExtendedSelection)
        self.objectList.itemDoubleClicked.connect(self.setEditMode)
        self.objectList.itemSelectionChanged.connect(self.objectSelectionChanged)
        self.objectList.setToolTip(
            self.tr(
                "Select object to start annotating for it. "
            )
        )
        first_label = None
        self.lbl2idx = {}
        if self._config.get("labels"):
            for idx, label in enumerate(self._config.get("labels")):
                item = self.uniqLabelList.createItemFromLabel(label)
                self.uniqLabelList.addItem(item)
                self.uniqLabelList.setItemLabel(item, label)
                self.lbl2idx[label] = idx + 1
                if idx == 0:
                    first_label = item
        self.label_dock = QtWidgets.QDockWidget(self.tr(u"Label List"), self)
        self.label_dock.setObjectName(u"Label List")
        self.label_dock.setWidget(self.uniqLabelList)

        first_object = None
        if self._config.get("max_number_of_objects"):
            for number in [str(nu) for nu in range(1, self._config.get("max_number_of_objects") + 1)]:
                item = self.objectList.createItemFromLabel(number)
                self.objectList.addItem(item)
                rgb = self._get_rgb_by_object(number)
                self.objectList.setItemLabel(item, number, rgb)
                if number == '1':
                    first_object = item
        self.object_dock = QtWidgets.QDockWidget(self.tr(u"Object List"), self)
        self.object_dock.setObjectName(u"Object List")
        self.object_dock.setWidget(self.objectList)

        self.fileSearch = QtWidgets.QLineEdit()
        self.fileSearch.setPlaceholderText(self.tr("Search Filename"))
        self.fileSearch.textChanged.connect(self.fileSearchChanged)
        self.fileListWidget = QtWidgets.QListWidget()
        self.fileListWidget.itemSelectionChanged.connect(
            self.fileSelectionChanged
        )
        fileListLayout = QtWidgets.QVBoxLayout()
        fileListLayout.setContentsMargins(0, 0, 0, 0)
        fileListLayout.setSpacing(0)
        fileListLayout.addWidget(self.fileSearch)
        fileListLayout.addWidget(self.fileListWidget)
        self.file_dock = QtWidgets.QDockWidget(self.tr(u"File List"), self)
        self.file_dock.setObjectName(u"Files")
        fileListWidget = QtWidgets.QWidget()
        fileListWidget.setLayout(fileListLayout)
        self.file_dock.setWidget(fileListWidget)

        self.zoomWidget = ZoomWidget()
        self.setAcceptDrops(True)

        self.canvas = self.labelList.canvas = Canvas(
            epsilon=self._config.get("epsilon"),
            double_click=self._config.get("canvas", {}).get("double_click"),
        )
        self.canvas.zoomRequest.connect(self.zoomRequest)

        scrollArea = QtWidgets.QScrollArea()
        scrollArea.setWidget(self.canvas)
        scrollArea.setWidgetResizable(True)
        self.scrollBars = {
            Qt.Vertical: scrollArea.verticalScrollBar(),
            Qt.Horizontal: scrollArea.horizontalScrollBar(),
        }
        self.canvas.scrollRequest.connect(self.scrollRequest)

        self.canvas.newShape.connect(self.newShape)
        self.canvas.shapeMoved.connect(self.editShape)
        self.canvas.selectionChanged.connect(self.shapeSelectionChanged)
        self.canvas.drawingPolygon.connect(self.toggleDrawingSensitive)

        #set defaults for label list and object list
        if first_label:
            self.uniqLabelList.setCurrentItem(first_label)
        if first_object:
            self.objectList.setCurrentItem(first_object)
            
        self.setCentralWidget(scrollArea)

        features = QtWidgets.QDockWidget.DockWidgetFeatures()
        for dock in ["flag_dock", "label_dock", "shape_dock", "file_dock"]:
            if self._config.get(dock, {}).get("closable"):
                features = features | QtWidgets.QDockWidget.DockWidgetClosable
            if self._config.get(dock, {}).get("floatable"):
                features = features | QtWidgets.QDockWidget.DockWidgetFloatable
            if self._config.get(dock, {}).get("movable"):
                features = features | QtWidgets.QDockWidget.DockWidgetMovable
            getattr(self, dock).setFeatures(features)
            if self._config.get(dock, {}).get("show") is False:
                getattr(self, dock).setVisible(False)

        self.addDockWidget(Qt.RightDockWidgetArea, self.flag_dock)
        self.addDockWidget(Qt.RightDockWidgetArea, self.label_dock)
        self.addDockWidget(Qt.RightDockWidgetArea, self.object_dock)
        self.addDockWidget(Qt.RightDockWidgetArea, self.shape_dock)
        self.addDockWidget(Qt.RightDockWidgetArea, self.file_dock)

        # Actions
        action = functools.partial(utils.newAction, self)
        shortcuts = self._config.get("shortcuts")
        quit = action(
            self.tr("&Quit"),
            self.close,
            shortcuts.get("quit"),
            "quit",
            self.tr("Quit application"),
        )
        open_ = action(
            self.tr("&Open"),
            self.openFile,
            shortcuts.get("open"),
            "open",
            self.tr("Open image or label file"),
        )
        opendir = action(
            self.tr("&Open Dir"),
            self.openDirDialog,
            shortcuts.get("open_dir"),
            "open",
            self.tr(u"Open Dir"),
        )
        video_kmeans = action(
            self.tr("&Extract video frames smartly"),
            self.kmeansVideo,
            icon = "open",
            tip = self.tr("Open video with Kmeans extraction"),
        )
        video_uniform = action(
            self.tr("&Extract video frames uniformly"),
            self.uniformVideo,
            icon = "open",
            tip = self.tr("Open video with uniform extraction"),
        )
        openJsonConfigFile = action(
            self.tr("&Open JSON config file"),
            self.openJSONConfig,
            None,
            "open",
            self.tr("Open JSON config file"),
        )
        openNextImg = action(
            self.tr("&Next Image"),
            self.openNextImg,
            shortcuts.get("open_next"),
            "next",
            self.tr(u"Open next (hold Ctl+Shift to copy labels)"),
            enabled=False,
        )
        openPrevImg = action(
            self.tr("&Prev Image"),
            self.openPrevImg,
            shortcuts.get("open_prev"),
            "prev",
            self.tr(u"Open prev (hold Ctl+Shift to copy labels)"),
            enabled=False,
        )
        openNextImgTrack = action(
            self.tr("&Next Tracking"),
            lambda: self.openNextImg(tracking=True),
            icon = "next",
            tip = self.tr(u"Open next image with current labels"),
            enabled=False,
        )
        openPrevImgTrack = action(
            self.tr("&Prev Tracking"),
            lambda: self.openPrevImg(tracking=True),
            icon = "prev",
            tip = self.tr(u"Open prev img with current labels"),
            enabled=False,
        )

        save = action(
            self.tr("&Save"),
            self.saveFile,
            shortcuts.get("save"),
            "save",
            self.tr("Save labels to file"),
            enabled=False,
        )
        saveAs = action(
            self.tr("&Save As"),
            self.saveFileAs,
            shortcuts.get("save_as"),
            "save-as",
            self.tr("Save labels to a different file"),
            enabled=False,
        )

        completePoints = action(
            self.tr("&Export all Files"),
            self.exportFiles,
            icon = "labels",
            tip = self.tr(u"Projects the points for all files and saves ina a JSON format"),
            enabled=False,
        )

        deleteFile = action(
            self.tr("&Delete File"),
            self.deleteFile,
            shortcuts.get("delete_file"),
            "delete",
            self.tr("Delete current label file"),
            enabled=False,
        )

        cleanFiles = action(
            self.tr("&Delete Non Labeled Images"),
            self.cleanFiles,
            shortcuts.get("delete_file"),
            "delete",
            self.tr("Delete non labeled images in the current directory"),
            enabled=False,
        )


        changeOutputDir = action(
            self.tr("&Change Output Dir"),
            slot=self.changeOutputDirDialog,
            shortcut=shortcuts.get("save_to"),
            icon="open",
            tip=self.tr(u"Change where annotations are loaded/saved"),
        )

        saveAuto = action(
            text=self.tr("Save &Automatically"),
            slot=lambda x: self.actions.saveAuto.setChecked(x),
            icon="save",
            tip=self.tr("Save automatically"),
            checkable=True,
            enabled=True,
        )
        saveAuto.setChecked(self._config.get("auto_save"))

        saveWithImageData = action(
            text="Save With Image Data",
            slot=self.enableSaveImageWithData,
            tip="Save image data in label file",
            checkable=True,
            checked=self._config.get("store_data"),
        )

        close = action(
            "&Close",
            self.closeFile,
            shortcuts.get("close"),
            "close",
            "Close current file",
        )

        toggle_keep_prev_mode = action(
            self.tr("Keep Previous Annotation"),
            self.toggleKeepPrevMode,
            shortcuts.get("toggle_keep_prev_mode"),
            None,
            self.tr('Toggle "keep pevious annotation" mode'),
            checkable=True,
        )
        toggle_keep_prev_mode.setChecked(self._config.get("keep_prev"))

        
        createMode = action(
            self.tr("Create Point"),
            lambda: self.toggleDrawMode(False, createMode="point"),
            shortcuts.get("create_point"),
            "objects",
            self.tr("Start drawing points"),
            enabled=False,
        )
        editMode = action(
            self.tr("Edit Points"),
            self.setEditMode,
            shortcuts.get("edit_polygon"),
            "edit",
            self.tr("Move and edit the selected points"),
            enabled=False,
        )

        delete = action(
            self.tr("Delete Points"),
            self.deleteSelectedShape,
            shortcuts.get("delete_polygon"),
            "cancel",
            self.tr("Delete the selected points"),
            enabled=False,
        )
        copy = action(
            self.tr("Copy Points"),
            self.copySelectedShape,
            shortcuts.get("duplicate_polygon"),
            "copy",
            self.tr("Copy the selected points"),
            enabled=False,
        )
        paste = action(
            self.tr('Paste Points'),
            self.pasteSelectedShapes,
            shortcuts.get("paste_polygon"),
            "paste",
            self.tr("Paste the selected points"),
            enabled=True,)
        undoLastPoint = action(
            self.tr("Undo last point"),
            self.canvas.undoLastPoint,
            shortcuts.get("undo_last_point"),
            "undo",
            self.tr("Undo last drawn point"),
            enabled=False,
        )
        addPointToEdge = action(
            text=self.tr("Add Point to Edge"),
            slot=self.canvas.addPointToEdge,
            shortcut=shortcuts.get("add_point_to_edge"),
            icon="edit",
            tip=self.tr("Add point to the nearest edge"),
            enabled=False,
        )
        removePoint = action(
            text="Remove Selected Point",
            slot=self.canvas.removeSelectedPoint,
            icon="edit",
            tip="Remove selected point from polygon",
            enabled=False,
        )

        undo = action(
            self.tr("Undo"),
            self.undoShapeEdit,
            shortcuts.get("undo"),
            "undo",
            self.tr("Undo last add and edit of shape"),
            enabled=False,
        )

        hideAll = action(
            self.tr("&Hide\nPolygons"),
            functools.partial(self.togglePolygons, False),
            icon="eye",
            tip=self.tr("Hide all polygons"),
            enabled=False,
        )
        showAll = action(
            self.tr("&Show\nPolygons"),
            functools.partial(self.togglePolygons, True),
            icon="eye",
            tip=self.tr("Show all polygons"),
            enabled=False,
        )

        help = action(
            self.tr("&Tutorial"),
            self.tutorial,
            icon="help",
            tip=self.tr("Show tutorial page"),
        )

        about = action(
            self.tr("&Version Info"),
            self.show_version,
            tip = self.tr("Shows version and other info"))
        check_lic = action(
            self.tr("&Check License"),
            self.check_lic,
            tip = self.tr("Checks if there is a valid license attached"))
        create_lic = action(
            self.tr("&Create License"),
            self.create_lic,
            tip = self.tr("Creates a License"),
            enabled = not isDeployed)

        zoom = QtWidgets.QWidgetAction(self)
        zoom.setDefaultWidget(self.zoomWidget)
        self.zoomWidget.setWhatsThis(
            self.tr(
                "Zoom in or out of the image. Also accessible with "
                "{} and {} from the canvas."
            ).format(
                utils.fmtShortcut(
                    "{},{}".format(shortcuts.get("zoom_in"), shortcuts.get("zoom_out"))
                ),
                utils.fmtShortcut(self.tr("Ctrl+Wheel")),
            )
        )
        self.zoomWidget.setEnabled(False)

        zoomIn = action(
            self.tr("Zoom &In"),
            functools.partial(self.addZoom, 1.1),
            shortcuts.get("zoom_in"),
            "zoom-in",
            self.tr("Increase zoom level"),
            enabled=False,
        )
        zoomOut = action(
            self.tr("&Zoom Out"),
            functools.partial(self.addZoom, 0.9),
            shortcuts.get("zoom_out"),
            "zoom-out",
            self.tr("Decrease zoom level"),
            enabled=False,
        )
        zoomOrg = action(
            self.tr("&Original size"),
            functools.partial(self.setZoom, 100),
            shortcuts.get("zoom_to_original"),
            "zoom",
            self.tr("Zoom to original size"),
            enabled=False,
        )
        fitWindow = action(
            self.tr("&Fit Window"),
            self.setFitWindow,
            shortcuts.get("fit_window"),
            "fit-window",
            self.tr("Zoom follows window size"),
            checkable=True,
            enabled=False,
        )
        fitWidth = action(
            self.tr("Fit &Width"),
            self.setFitWidth,
            shortcuts.get("fit_width"),
            "fit-width",
            self.tr("Zoom follows window width"),
            checkable=True,
            enabled=False,
        )
        brightnessContrast = action(
            "&Brightness Contrast",
            self.brightnessContrast,
            None,
            "color",
            "Adjust brightness and contrast",
            enabled=False,
        )
        # Group zoom controls into a list for easier toggling.
        zoomActions = (
            self.zoomWidget,
            zoomIn,
            zoomOut,
            zoomOrg,
            fitWindow,
            fitWidth,
        )
        self.zoomMode = self.FIT_WINDOW
        fitWindow.setChecked(Qt.Checked)
        self.scalers = {
            self.FIT_WINDOW: self.scaleFitWindow,
            self.FIT_WIDTH: self.scaleFitWidth,
            # Set to one to scale to 100% when loading files.
            self.MANUAL_ZOOM: lambda: 1,
        }

        edit = action(
            self.tr("&Edit Label"),
            self.editLabel,
            shortcuts.get("edit_label"),
            "edit",
            self.tr("Modify the label of the selected polygon"),
            enabled=False,
        )

        fill_drawing = action(
            self.tr("Fill Drawing Polygon"),
            self.canvas.setFillDrawing,
            None,
            "color",
            self.tr("Fill polygon while drawing"),
            checkable=True,
            enabled=True,
        )
        fill_drawing.trigger()

        axis_3d = action(
            self.tr("&3D Axes"),
            self.compute_axis,
            None,
            "axis",
            self.tr("Display the 3D axes calculated by the labels"),
            checkable=True, #UD
            enabled = True
        )

        shape_3d = action(
            self.tr("&3D Shape"),
            self.compute_shape,
            None,
            "shape",
            self.tr("Display the 3D shape calculated by the labels"),
            checkable=True, #UD
            enabled = True
        )
        clear = action(
                self.tr('&Clear Shape'),
                self.clear_shape,
                shortcuts.get('clear'), 
                "cancel",
                self.tr("Clear all the shapes and axes projected"),
                enabled=True)

        # Lavel list context menu.
        labelMenu = QtWidgets.QMenu()
        utils.addActions(labelMenu, (edit, delete))
        self.labelList.setContextMenuPolicy(Qt.CustomContextMenu)
        self.labelList.customContextMenuRequested.connect(
            self.popLabelListMenu
        )

        # Store actions for further handling.
        self.actions = utils.struct(
            saveAuto=saveAuto,
            saveWithImageData=saveWithImageData,
            changeOutputDir=changeOutputDir,
            save=save,
            saveAs=saveAs,
            open=open_,
            close=close,
            deleteFile=deleteFile,
            toggleKeepPrevMode=toggle_keep_prev_mode,
            delete=delete,
            edit=edit,
            copy=copy,
            paste=paste,
            undoLastPoint=undoLastPoint,
            undo=undo,
            addPointToEdge=addPointToEdge,
            removePoint=removePoint,
            createMode=createMode,
            editMode=editMode,
            zoom=zoom,
            zoomIn=zoomIn,
            zoomOut=zoomOut,
            zoomOrg=zoomOrg,
            fitWindow=fitWindow,
            fitWidth=fitWidth,
            brightnessContrast=brightnessContrast,
            zoomActions=zoomActions,
            openNextImg=openNextImg,
            openPrevImg=openPrevImg,
            openNextImgTrack = openNextImgTrack,
            openPrevImgTrack = openPrevImgTrack,
            axis_3d = axis_3d,
            shape_3d = shape_3d,
            clear = clear,
            completePoints = completePoints,
            cleanFiles = cleanFiles,
            video_kmeans = video_kmeans,
            video_uniform = video_uniform,
            fileMenuActions=(open_, opendir, save, saveAs, close, quit),
            tool=(),
            # XXX: need to add some actions here to activate the shortcut
            editMenu=(
                edit,
                copy,
                paste,
                delete,
                None,
                undo,
                undoLastPoint,
                None,
                addPointToEdge,
                toggle_keep_prev_mode,
                None,
                completePoints,
                None,
                cleanFiles
            ),
            # menu shown at right click
            menu=(
                # createMode,
                # createRectangleMode,
                # createCircleMode,
                # createLineMode,
                # createPointMode,
                # createLineStripMode,
                # editMode,
                # edit,
                # copy,
                # paste,
                # delete,
                # undo,
                # undoLastPoint,
                # addPointToEdge,
                # removePoint,
            ),
            onLoadActive=(
                close,
                createMode,
                editMode,
                brightnessContrast,
            ),
            onShapesPresent=(saveAs, hideAll, showAll),
        )

        self.canvas.edgeSelected.connect(self.canvasShapeEdgeSelected)
        self.canvas.vertexSelected.connect(self.actions.removePoint.setEnabled)

        self.menus = utils.struct(
            file=self.menu(self.tr("&File")),
            edit=self.menu(self.tr("&Edit")),
            view=self.menu(self.tr("&View")),
            help=self.menu(self.tr("&Help")),
            recentFiles=QtWidgets.QMenu(self.tr("Open &Recent")),
            labelList=labelMenu,
        )

        utils.addActions(
            self.menus.file,
            (
                open_,
                openNextImg,
                openPrevImg,
                openNextImgTrack,
                openPrevImgTrack,
                opendir,
                openJsonConfigFile,
                self.menus.recentFiles,
                video_kmeans,
                video_uniform,
                save,
                saveAs,
                saveAuto,
                changeOutputDir,
                saveWithImageData,
                close,
                deleteFile,
                None,
                quit,
            ),
        )
        utils.addActions(self.menus.help, (help, about, check_lic, create_lic))
        utils.addActions(
            self.menus.view,
            (
                self.flag_dock.toggleViewAction(),
                self.label_dock.toggleViewAction(),
                self.object_dock.toggleViewAction(),
                self.shape_dock.toggleViewAction(),
                self.file_dock.toggleViewAction(),
                None,
                fill_drawing,
                None,
                hideAll,
                showAll,
                None,
                zoomIn,
                zoomOut,
                zoomOrg,
                None,
                fitWindow,
                fitWidth,
                None,
                brightnessContrast,
                None,
                axis_3d,
                shape_3d, 
                clear,
                ),
        )

        self.menus.file.aboutToShow.connect(self.updateFileMenu)

        # Custom context menu for the canvas widget:
        utils.addActions(self.canvas.menus[0], self.actions.menu)
        utils.addActions(
            self.canvas.menus[1],
            (
                action("&Copy here", self.copyShape),
                action("&Move here", self.moveShape),
            ),
        )

        self.tools = self.toolbar("Tools")
        # Menu buttons on Left
        self.actions.tool = (
            opendir,
            openNextImgTrack,
            openPrevImgTrack,
            None,
            createMode,
            editMode,
            #save,  # not in use           
            copy,
            paste,
            delete,
            undo,
            shape_3d,
            axis_3d,
            clear,            
            brightnessContrast,
            None,
            zoom,
            fitWidth,
            open_,            
            openNextImg,
            openPrevImg,


        )

        self.statusBar().showMessage(self.tr("%s started.") % __appname__)
        self.statusBar().show()

        if output_file is not None and self._config.get("auto_save"):
            logger.warn(
                "If `auto_save` argument is True, `output_file` argument "
                "is ignored and output filename is automatically "
                "set as IMAGE_BASENAME.json."
            )
        self.output_file = output_file
        self.output_dir = output_dir

        # Application state.
        self.image = QtGui.QImage()
        self.imagePath = None
        self.imageType = None
        self.recentFiles = []
        self.maxRecent = 7
        self.otherData = None
        self.zoom_level = 100
        self.fit_window = False
        self.zoom_values = {}  # key=filename, value=(zoom_mode, zoom_value)
        self.brightnessContrast_values = {}
        self.scroll_values = {
            Qt.Horizontal: {},
            Qt.Vertical: {},
        }  # key=filename, value=scroll_value
        self.jsonfile = None
        if self._config.get('jsonfile', None):
            self.jsonfile = osp.abspath(self._config.get("jsonfile"))
            if not osp.exists(self.jsonfile):
                self.jsonfile = None
           
        self.license = LicenseManager()

        self.added_shapes = None
        self.d = None
        
        # Restore application settings.
        self.settings = QtCore.QSettings("labelme", "labelme")
        # FIXME: QSettings.value can return None on PyQt4
        self.recentFiles = self.settings.value("recentFiles", []) or []
        size = self.settings.value("window/size", QtCore.QSize(600, 500))
        position = self.settings.value("window/position", QtCore.QPoint(0, 0))
        self.resize(size)
        self.move(position)
        # or simply:
        # self.restoreGeometry(settings['window/geometry']
        self.restoreState(
            self.settings.value("window/state", QtCore.QByteArray())
        )

        if filename is not None and osp.isdir(filename):
            self.importDirImages(filename, load=False)
        elif self.lastOpenDir is not None:
            self.importDirImages(self.lastOpenDir)
        else:
            self.filename = filename

        if self._config.get("file_search"):
            self.fileSearch.setText(self._config.get("file_search"))
            self.fileSearchChanged()

        # XXX: Could be completely declarative.
        

        # Populate the File menu dynamically.
        self.updateFileMenu()
        # Since loading the file may take some time,
        # make sure it runs in the background.
        # if self.filename is not None:
        #     self.queueEvent(functools.partial(self.loadFile, self.filename))
        # elif self.lastOpenImg is not None:
        #     self.queueEvent(functools.partial(self.loadFile, self.lastOpenImg))
        # Callbacks:
        self.zoomWidget.valueChanged.connect(self.paintCanvas)

        self.populateModeActions()
        
        if self.jsonfile is None:
            mb = QtWidgets.QMessageBox
            msg = self.tr(
                "No JSON file was found. This may cause issues with labeling. Do you want to add a JSON File before continuing?"
            )
            answer = mb.information(self, self.tr("No JSON File Availible"), msg, mb.Yes | mb.No)
            if answer == mb.Yes:
                self.openJSONConfig()
        # self.firstStart = True
        # if self.firstStart:
        #    QWhatsThis.enterWhatsThisMode()

    def menu(self, title, actions=None):
        menu = self.menuBar().addMenu(title)
        if actions:
            utils.addActions(menu, actions)
        return menu

    def toolbar(self, title, actions=None):
        toolbar = ToolBar(title)
        toolbar.setObjectName("%sToolBar" % title)
        # toolbar.setOrientation(Qt.Vertical)
        toolbar.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        if actions:
            utils.addActions(toolbar, actions)
        self.addToolBar(Qt.LeftToolBarArea, toolbar)
        return toolbar

    # Support Functions

    def noShapes(self):
        return not len(self.labelList)

    def populateModeActions(self):
        tool, menu = self.actions.tool, self.actions.menu
        self.tools.clear()
        utils.addActions(self.tools, tool)
        self.canvas.menus[0].clear()
        utils.addActions(self.canvas.menus[0], menu)
        self.menus.edit.clear()
        actions = (
            self.actions.createMode,
            self.actions.editMode,
        )
        utils.addActions(self.menus.edit, actions + self.actions.editMenu)
        

    def setDirty(self):
        if self._config.get("auto_save") or self.actions.saveAuto.isChecked():
            self._config["auto_save"] = True
            self.updateConfig()
            if self.labelFile:
                label_file = self.labelFile.filename
            else:
                label_file = osp.splitext(self.imagePath)[0] + ".json"
            if self.output_dir:
                label_file_without_path = osp.basename(label_file)
                label_file = osp.join(self.output_dir, label_file_without_path)
            self.saveLabels(label_file)
            return
        self.dirty = True
        self.actions.save.setEnabled(True)
        self.actions.undo.setEnabled(self.canvas.isShapeRestorable)
        title = __appname__
        if self.filename is not None:
            title = "{} - {}*".format(title, self.filename)
        self.setWindowTitle(title)

    def setClean(self):
        self.dirty = False
        self.actions.save.setEnabled(False)
        self.actions.createMode.setEnabled(True)
        title = __appname__
        if self.filename is not None:
            title = "{} - {}".format(title, self.filename)
        self.setWindowTitle(title)

        if self.hasLabelFile():
            self.actions.deleteFile.setEnabled(True)
        else:
            self.actions.deleteFile.setEnabled(False)

    def toggleActions(self, value=True):
        """Enable/Disable widgets which depend on an opened image."""
        for z in self.actions.zoomActions:
            z.setEnabled(value)
        if self.jsonfile:
            for action in self.actions.onLoadActive:
                action.setEnabled(value)

    def canvasShapeEdgeSelected(self, selected, shape):
        self.actions.addPointToEdge.setEnabled(
            selected and shape and shape.canAddPoint()
        )

    def queueEvent(self, function):
        QtCore.QTimer.singleShot(0, function)

    def status(self, message, delay=5000):
        self.statusBar().showMessage(message, delay)
        self.Print(message)

    def resetState(self):
        self.labelList.clear()
        self.filename = None
        self.imagePath = None
        self.imageData = None
        self.labelFile = None
        self.otherData = None
        self.canvas.resetState()

    def currentItem(self):
        items = self.labelList.selectedItems()
        if items:
            return items[0]
        return None

    def addRecentFile(self, filename):
        if filename in self.recentFiles:
            self.recentFiles.remove(filename)
        elif len(self.recentFiles) >= self.maxRecent:
            self.recentFiles.pop()
        self.recentFiles.insert(0, filename)

    # Callbacks

    def undoShapeEdit(self):
        self.canvas.restoreShape()
        self.labelList.clear()
        self.loadShapes(self.canvas.shapes)
        self.actions.undo.setEnabled(self.canvas.isShapeRestorable)
        self.setDirty()

    def tutorial(self):
        url = "https://drive.google.com/file/d/10T0fwVJaPxoY40KBUZBKnqgSlm-nv5Ya/view?usp=sharing"  # NOQA
        webbrowser.open(url)

    def show_version(self):

        # if not self.d:
        self.d = QtWidgets.QDialog()
        self.d.setWindowTitle("Version")

        layout = QtWidgets.QVBoxLayout()
        message = QtWidgets.QLabel("Current Version:  <b>%s</b>" % __version__)
        layout.addWidget(message)
        self.d.setLayout(layout)
        self.d.resize(320, 70)
        self.d.show()

        # d.activateWindow()

    def create_lic(self):
        licFile = QtWidgets.QFileDialog.getOpenFileName(
            self,
            self.tr("%s - Select License file") % __appname__,
            '.' )
        # check if cancel
        if not licFile[0]:
            print('User canceled')
            self.status('User Canceled')
            return None
        
        # read params
        
        txt, ok = QtWidgets.QInputDialog.getText(self, "License Code", "Input code in structure: Y,M,D")
        if ok:
            if len(txt) < 2:
                title = self.tr('Input is not valid'),
                msg = self.tr('Name must have at least 2 chars')
            
                
            else:
            
                try:
                    expYear,expMonth,expDay = txt.split(',')
                    self.license.Recode(licFile[0], int(expYear) , int(expMonth) , int(expDay))
                    title = self.tr('Success')
                    msg = self.tr('License file is created')
                except:
                    title = self.tr('Input is not valid')
                    msg = self.tr('Must be : Y,M,D')
            
            mb = QtWidgets.QMessageBox
            mb.information(
                        self,
                        title,
                        msg)
            
    def check_lic(self):
        licFile = QtWidgets.QFileDialog.getOpenFileName(
            self,
            self.tr("%s - Select License file") % __appname__,
            '.' )
        # check if cancel
        if not licFile[0]:
            print('User canceled')
            self.status('User Canceled')
            return None                
        try:
            ret = self.license.Check(licFile[0])
            if ret: 
                title = self.tr('Success')
                msg = self.tr('License file is OK')  
            else:
                title = self.tr('Failure')
                msg = self.tr('License file is not valid or expired')  
        except:
            title = self.tr('Failure')
            msg = self.tr('Something wrong with license file')
            
        mb = QtWidgets.QMessageBox
        mb.information(
                    self,
                    title,
                    msg)

    def toggleDrawingSensitive(self, drawing=True):
        """Toggle drawing sensitive.

        In the middle of drawing, toggling between modes should be disabled.
        """
        self.actions.editMode.setEnabled(not drawing)
        self.actions.undoLastPoint.setEnabled(drawing)
        self.actions.undo.setEnabled(not drawing)
        self.actions.delete.setEnabled(not drawing)

    def toggleDrawMode(self, edit=True, createMode="point"):
        self.canvas.setEditing(edit)
        self.canvas.createMode = createMode
        if edit:
            self.actions.createMode.setEnabled(True)
        else:
            self.actions.createMode.setEnabled(False)
            
        
        self.actions.editMode.setEnabled(not edit)

    def setEditMode(self):
        self.toggleDrawMode(True)
    def setCreateMode(self):
        self.toggleDrawMode(False)
        
    def updateFileMenu(self):
        current = self.filename

        def exists(filename):
            return osp.exists(str(filename))

        menu = self.menus.recentFiles
        menu.clear()
        files = [f for f in self.recentFiles if f != current and exists(f)]
        for i, f in enumerate(files):
            icon = utils.newIcon("labels")
            action = QtWidgets.QAction(
                icon, "&%d %s" % (i + 1, QtCore.QFileInfo(f).fileName()), self
            )
            action.triggered.connect(functools.partial(self.loadRecent, f))
            menu.addAction(action)

    def popLabelListMenu(self, point):
        self.menus.labelList.exec_(self.labelList.mapToGlobal(point))

    def validateLabel(self, label):
        # no validation
        if self._config.get("validate_label") is None:
            return True

        for i in range(self.uniqLabelList.count()):
            label_i = self.uniqLabelList.item(i).data(Qt.UserRole)
            if self._config.get("validate_label") in ["exact"]:
                if label_i == label:
                    return True
        return False

    def editLabel(self, item=None):
        if item and not isinstance(item, LabelListWidgetItem):
            raise TypeError("item must be LabelListWidgetItem type")

        if not self.canvas.editing():
            return
        if not item:
            item = self.currentItem()
        if item is None:
            return
        shape = item.shape()
        if shape is None:
            return
        text, flags, group_id = self.labelDialog.popUp(
            text=shape.label,
            flags=shape.flags,
            group_id=shape.group_id,
        )
        if text is None:
            return
        if not self.validateLabel(text):
            self.errorMessage(
                self.tr("Invalid label"),
                self.tr("Invalid label '{}' with validation type '{}'").format(
                    text, self._config.get("validate_label")
                ),
            )
            return
        shape.label = text
        shape.flags = flags
        shape.group_id = group_id
        if shape.group_id is None:
            item.setText(shape.label)
        else:
            item.setText("{} ({})".format(shape.label, shape.group_id))
        self.setDirty()
        if not self.uniqLabelList.findItemsByLabel(shape.label):
            item = QtWidgets.QListWidgetItem()
            item.setData(Qt.UserRole, shape.label)
            self.uniqLabelList.addItem(item)

    def fileSearchChanged(self):
        self.importDirImages(
            self.lastOpenDir,
            pattern=self.fileSearch.text(),
            load=False,
        )

    def fileSelectionChanged(self):
        items = self.fileListWidget.selectedItems()
        if not items:
            return
        item = items[0]

        if not self.mayContinue():
            return

        currIndex = self.imageList.index(str(item.text()))
        if currIndex < len(self.imageList):
            filename = self.imageList[currIndex]
            if filename:
                self.loadFile(filename)

    # React to canvas signals.
    def shapeSelectionChanged(self, selected_shapes):
        self._noSelectionSlot = True
        for shape in self.canvas.selectedShapes:
            shape.selected = False
        self.labelList.clearSelection()
        self.canvas.selectedShapes = selected_shapes
        for shape in self.canvas.selectedShapes:
            if shape.isEditable():
                shape.selected = True
                item = self.labelList.findItemByShape(shape)
                self.labelList.selectItem(item)
                self.labelList.scrollToItem(item)
            else:
                self.canvas.selectedShapes.remove(shape)
        self._noSelectionSlot = False
        n_selected = len(selected_shapes)
        self.actions.delete.setEnabled(n_selected)
        self.actions.copy.setEnabled(n_selected)
        # self.actions.paste.setEnabled(n_selected)
        self.actions.edit.setEnabled(n_selected == 1)

    def addLabel(self, shape, init=False):
        if shape.group_id is None:
            text = shape.label
        else:
            text = "{}-{}".format(shape.group_id, shape.label)
        label_list_item = LabelListWidgetItem(text, shape)
        self.labelList.addItem(label_list_item)
        if not self.uniqLabelList.findItemsByLabel(shape.label):
            item = self.uniqLabelList.createItemFromLabel(shape.label)
            self.uniqLabelList.addItem(item)
            rgb = self._get_rgb_by_label(shape.label)
            self.uniqLabelList.setItemLabel(item, shape.label, rgb)
        self.labelDialog.addLabelHistory(shape.label)
        for action in self.actions.onShapesPresent:
            action.setEnabled(True)
        self.actions.shape_3d.setEnabled(True)
        self.actions.completePoints.setEnabled(True)
        self.actions.cleanFiles.setEnabled(True)
        rgb = self._get_rgb_by_object(shape.group_id) if shape.group_id is not None else self._get_rgb_by_label(
            shape.label)

        r, g, b = rgb
        label_list_item.setText(
            '{} <font color="#{:02x}{:02x}{:02x}">●</font>'.format(
                text, r, g, b
            )
        )
        shape.line_color = QtGui.QColor(r, g, b)
        shape.vertex_fill_color = QtGui.QColor(r, g, b)
        shape.hvertex_fill_color = QtGui.QColor(255, 255, 255)
        shape.fill_color = QtGui.QColor(r, g, b, 128)
        shape.select_line_color = QtGui.QColor(255, 255, 255)
        shape.select_fill_color = QtGui.QColor(r, g, b, 155)
        
        #try to complete the points if enough labels:
        #TODO: how to not do this action a million times
        if len(self.labelList) > 4 and not init:
            self.compute_shape()
            self.compute_axis()


    def convertQImageToMat(self, incomingImage):
        '''  Converts a QImage into an opencv MAT format
        from https://stackoverflow.com/questions/18406149/pyqt-pyside-how-do-i-convert-qimage-into-opencvs-mat-format'''

        incomingImage = incomingImage.convertToFormat(4)

        width = incomingImage.width()
        height = incomingImage.height()

        ptr = incomingImage.bits()
        ptr.setsize(incomingImage.byteCount())
        arr = np.array(ptr).reshape(height, width, 4)  #  Copies the data
        return arr

    def _get_rgb_by_label(self, label):
        if self._config.get("shape_color") == "auto":
            item = self.uniqLabelList.findItemsByLabel(label)[0]
            label_id = self.uniqLabelList.indexFromItem(item).row() + 1
            label_id += self._config.get("shift_auto_shape_color")
            return LABEL_COLORMAP[label_id % len(LABEL_COLORMAP)]
        elif (
                self._config.get("shape_color") == "manual"
                and self._config.get("label_colors")
                and label in self._config.get("label_colors")
        ):
            return self._config["label_colors"][label]
        elif self._config.get("default_shape_color"):
            return self._config["default_shape_color"]

    def _get_rgb_by_object(self, label):
        if self._config.get("shape_color") == "auto":
            item = self.objectList.findItemsByLabel(label)[0]
            label_id = self.objectList.indexFromItem(item).row() + 1
            label_id += self._config.get("shift_auto_shape_color")
            return LABEL_COLORMAP[label_id % len(LABEL_COLORMAP)]
        elif (
                self._config.get("shape_color") == "manual"
                and self._config.get("label_colors")
                and label in self._config.get("label_colors")
        ):
            return self._config["label_colors"][label]
        elif self._config.get("default_shape_color"):
            return self._config["default_shape_color"]

    def remLabels(self, shapes):
        for shape in shapes:
            item = self.labelList.findItemByShape(shape)
            self.labelList.removeItem(item)

    def loadShapes(self, shapes, replace=True):
        self._noSelectionSlot = True
        for shape in shapes:
            self.addLabel(shape, init=True)
        self.labelList.clearSelection()
        self.objectList.clearSelection()
        self._noSelectionSlot = False
        self.canvas.loadShapes(shapes, replace=replace)
        g_ids = set()
        for shape in shapes:
            g_id = shape.group_id
            g_ids.add(g_id)
        for g_id in g_ids:
            item = self.objectList.findItemsByLabel(g_id)[0]
            item.setSelected(True)
        
        self.compute_shape()
        self.compute_axis()
        
#TODO: add a check for if label doesn't exist
    def loadLabels(self, shapes):
        s = []
#        try:
#            fid = open(self.jsonfile,'rt'); data = json.load(fid); fid.close()
#        except:
#            print('Can not find %s' %str(self.jsonfile))
#            return
        
        data = self.loadParamsFromJson()
        if data is None:
            return
        
        json_labels = data.get('RoiList')
        for shape in shapes:
            label = shape.get("label")
            if label not in json_labels:
                print('Label does not exist')
                continue
            points = shape.get("points")
            shape_type = shape.get("shape_type")
            flags = shape.get("flags")
            group_id = shape.get("group_id")
            other_data = shape.get("other_data")

            #UD protect from None
            if flags is None:
                flags = {}

            shape = Shape(
                label=label,
                shape_type=shape_type,
                group_id=group_id,
            )
            for x, y in points:
                shape.addPoint(QtCore.QPointF(x, y))
            shape.close()

            default_flags = {}
            if self._config.get("label_flags"):
                for pattern, keys in self._config.get("label_flags").items():
                    if re.match(pattern, label):
                        for key in keys:
                            default_flags[key] = False
            shape.flags = default_flags
            shape.flags.update(flags)
            shape.other_data = other_data

            s.append(shape)
        self.loadShapes(s)

    def loadFlags(self, flags):
        self.flag_widget.clear()
        for key, flag in flags.items():
            item = QtWidgets.QListWidgetItem(key)
            item.setFlags(item.flags() | Qt.ItemIsUserCheckable)
            item.setCheckState(Qt.Checked if flag else Qt.Unchecked)
            self.flag_widget.addItem(item)

    def get_object_info(self):
        dict_obj = {}
        for item in self.labelList:
            cur_shape = item.shape()
            obj_idx = cur_shape.group_id
            # label = cur_shape.label
            if dict_obj.get(obj_idx) is None: 
                dict_obj[obj_idx] = { "objectId": int(obj_idx), "pointNum": 0} #"labels": [], "points": []
            # dict_obj[obj_idx]["labels"].append(label)
            dict_obj[obj_idx]["pointNum"] += 1
            # dict_obj[obj_idx]["points"].append([cur_shape.points[0].x(), cur_shape.points[0].y()])
            
        return len(dict_obj.keys()), list(dict_obj.values())

    def saveLabels(self, filename):
        imagePath = osp.abspath(osp.join(self.imagePath, osp.dirname(filename)))
        # if osp.exists(imagePath):
        #     self.updateFile(filename, project)
        lf = LabelFile()

        shapes = {}
        objectNum, objectInfo = self.get_object_info()
        shapes['manual'] = [self.format_shape(item.shape()) for item in self.labelList]
        
        if self.labelFile:
            shapes['projected'] = self.labelFile.projectedShapes
        flags = {}
        for i in range(self.flag_widget.count()):
            item = self.flag_widget.item(i)
            key = item.text()
            flag = item.checkState() == Qt.Checked
            flags[key] = flag
        try:

            name = osp.split(filename)[1]
            ImageName = osp.splitext(name)[0] + self.imageType
            imageData = self.imageData if self._config.get("store_data") else None
            if osp.dirname(filename) and not osp.exists(osp.dirname(filename)):
                os.makedirs(osp.dirname(filename))
            lf.save(
                filename=filename,
                shapes=shapes,
                imagePath=imagePath,
                imageData=imageData,
                imageHeight=self.image.height(),
                imageWidth=self.image.width(),
                otherData=self.otherData,
                flags=flags,
                objectNum=objectNum,
                objectInfo=objectInfo,
                ImageName = ImageName
            )
            self.labelFile = lf
            items = self.fileListWidget.findItems(
                self.imagePath, Qt.MatchExactly
            )
            if len(items) > 0:
                if len(items) != 1:
                    raise RuntimeError("There are duplicate files.")
                items[0].setCheckState(Qt.Checked)
            # disable allows next and previous image to proceed
            # self.filename = filename
            return True
        except LabelFileError as e:
            self.errorMessage(
                self.tr("Error saving label data"), self.tr("<b>%s</b>") % e
            )
            return False

    def completeShapes(self):
        objectNum, objectInfo = self.get_object_info()
        shapes_projected =[]
        total_points = []
        for num in range(objectNum):
            #difference between self.labelList and self._config["labels"]
            labelShapes = [i.shape() for i in self.labelList]
            # labels = set(objectInfo[num]["labels"])
            id = str(objectInfo[num].get("objectId"))
            # labels_dict = dict(zip([j.label for j in labelShapes if str(j.group_id) == id], [j for j in labelShapes if str(j.group_id) == id]))
            labels = [j.label for j in labelShapes if str(j.group_id) == id]
            old_points = [[shape.points[0].x(), shape.points[0].y()] for shape in labelShapes if str(shape.group_id) == id]
            
            points = self.projectPoints(labels, old_points)
            if points:
                object_points =[]
                #UD - allowing for points to be outside
                for point in points:
                    if point[0] > self.image.width() or point[1] > self.image.height() or point[0] < 0 or point[1] < 0:
                        print(str(point), " in Object Number ", str(num + 1), " out of the image")
                        self.status("some points are out of the image '{}'".format(str(num+1)))
                        #return None
                total_points.append(points)
                objectInfo[num]["pointNum"] = len(points)
                objectInfo[num]["objectId"] = num + 1
                for label, point in zip( self._config.get('labels'), points):
                    # shape = labels_dict.get(label, None)
                    shape = Shape(
                        label=label,
                        shape_type="point",
                        group_id=str(num+1),
                        flags = {},
                        projected=True
                    )
                    shape.close()
                    shape.addPoint(QtCore.QPointF(point[0], point[1]))
                    # if label in labels_dict:
                    #     shape.projected = False
                    #     # shape.addPoint(QtCore.QPointF(point[0], point[1]))
                    #     shapes_manual.append(shape)
                    # else:
                    # shape.projected = True
                    # shape.addPoint(QtCore.QPointF(point[0], point[1]))
                    object_points.append(shape)
                shapes_projected.append(object_points)
            elif points == []:
                self.errorMessage(
                    "Configuration not found",
                    "Could not find a possible solution for object '{}'. Either add more labels or edit current labels".format(str(num+1)),
                )
            else:
                return None

        if len(total_points) == objectNum:
            # shapesm = [self.format_shape(s) for s in shapes_manual]
            shapesp = [[self.format_shape(s) for s in obj] for obj in shapes_projected]
            logger.info("Shapes completed")

            return shapesp
        else:
            return None

    def format_shape(self, s):
            data = s.other_data.copy()
            data.update(
                dict(
                    label=s.label.encode("utf-8") if PY2 else s.label,
                    points=[(p.x(), p.y()) for p in s.points],
                    group_id=s.group_id,
                    shape_type=s.shape_type,
                    flags=s.flags,
                    projected = s.projected
                )
            )
            return data

    def copySelectedShape(self):
        self.added_shapes = self.canvas.copySelectedShapes()
        self.labelList.clearSelection()
        
        
    def pasteSelectedShapes(self):
        if not self.added_shapes:
            return
        # group_ids = self.objectList.selectedItems()
        # shapes = []
        # shape_ids = set()
        for shape in self.added_shapes:
            # obj_id = shape.group_id
            # shape_ids.add(obj_id)
            
        
            
            # shape = self.added_shapes[i]
            # if i == len(group_ids):
            #     break
            # obj = group_ids[i].data(Qt.UserRole)
            # shape.group_id = obj
            self.addLabel(shape, init=True)
            # shapes.append(shape)
        self.canvas.pasteShapes(self.added_shapes)
        self.setDirty()
        self.added_shapes = None
        
    def labelSelectionChanged(self):
        if self._noSelectionSlot:
            return
        if self.canvas.editing():
            selected_shapes = []
            for item in self.labelList.selectedItems():
                selected_shapes.append(item.shape())
            if selected_shapes:
                self.canvas.selectShapes(selected_shapes)
            else:
                self.canvas.deSelectShape()

    def objectSelectionChanged(self):
        if self._noSelectionSlot:
            return
        groups = self.objectList.selectedItems()
        all_shapes = []
        if self.canvas.editing() and groups:
            for i in range(len(groups)):
                selected_object_number = groups[i].data(Qt.UserRole)
                selected_shapes = []
                for item in self.labelList:
                    if str(item.shape().group_id) == selected_object_number:
                        selected_shapes.append(item.shape())
                if selected_shapes:
                    all_shapes.extend(selected_shapes)
        if all_shapes:
            self.canvas.selectShapes(all_shapes)
        else:
            self.canvas.deSelectShape()

    def labelItemChanged(self, item):
        shape = item.shape()
        self.canvas.setShapeVisible(shape, item.checkState() == Qt.Checked)

    def labelOrderChanged(self):
        self.setDirty()
        self.canvas.loadShapes([item.shape() for item in self.labelList])

    # Callback functions:

    def newShape(self):
        """Pop-up and give focus to the label editor.

        position MUST be in global coordinates.
        """
        items = self.uniqLabelList.selectedItems()
        groups = self.objectList.selectedItems()
        text = None
        if items:
            text = items[0].data(Qt.UserRole)
        flags = {}
        group_id = groups[0].data(Qt.UserRole) if len(groups) == 1 else None

        if text is None or group_id is None:
            self.errorMessage(self.tr("Invalid Label or Object"), self.tr("You have to select one Label and one Object"))
            text = ""
        else:
            if self._config.get("display_label_popup") or not text:
                previous_text = self.labelDialog.edit.text()
                text, flags, group_id = self.labelDialog.popUp(text, group_id=group_id)
                if not text:
                    self.labelDialog.edit.setText(previous_text)

        if text and not self.validateLabel(text):
            self.errorMessage(
                self.tr("Invalid label"),
                self.tr("Invalid label '{}' with validation type '{}'").format(
                    text, self._config.get("validate_label")
                ),
            )
            text = ""
        if text:
            self.labelList.clearSelection()
            shape = self.canvas.setLastLabel(text, flags, group_id=group_id)
            # shape.group_id = group_id
            self.addLabel(shape)
            self.actions.editMode.setEnabled(True)
            self.actions.undoLastPoint.setEnabled(False)
            self.actions.undo.setEnabled(True)
            self.setDirty()
        else:
            self.canvas.undoLastLine()
            self.canvas.shapesBackups.pop()
            
    def editShape(self):
        self.setDirty()
        self.compute_shape()
        self.compute_axis()
        
    def compute_axis(self):
        
        if not self.actions.axis_3d.isChecked():
            return
#        # disable shape show
#        if not self.actions.shape_3d.isChecked():
#            self.actions.shape_3d.toggle()        
            
        #print('UD axis')
        
        axis_size = self._config.get('axis_size', 10)
        points3d = [[0,0,0], [axis_size,0,0], [0,axis_size,0], [0,0,axis_size]]
        #project the points, like projectPoints
        labelShapes = [i.shape() for i in self.labelList]
        axis_points = []
        object_nums = []
        groups = self.objectList.selectedItems()
#        if self.jsonfile:
#            try:
#                fid = open(self.jsonfile,'rt'); params = json.load(fid); fid.close()
#            except Exception as e:
#                print(e)
#                self.errorMessage("JSON file not correct - check the error above",
#                "No uploaded JSON File",
#                )                
#        else:
#            self.errorMessage(
#                "JSON file not correct",
#                "No uploaded JSON File",
#            )
#            return None
        
        params = self.loadParamsFromJson()
        if params is None:
            return 
        
        #this is the object we have selected
        for i in range(len(groups)):
            object_id = groups[i].data(Qt.UserRole)
            points = [[shape.points[0].x(), shape.points[0].y()] for shape in labelShapes if str(shape.group_id) == object_id]
            if len(points)<=2:
                print("Object {} has less than three points labeled".format(str(object_id)))
                self.status("Object {} has less than three points labeled".format(str(object_id)))
                continue 
            labels = [j.label for j in labelShapes if str(j.group_id) == object_id]
            points2D = np.array(points) #2d points on image
            try:
                indexes = np.array([int(self.lbl2idx[label]) for label in labels])
            except KeyError:
                self.errorMessage(
                    "JSON file not correct",
                    "Uploaded JSON file isn't correct: {}".format(osp.relpath(self.jsonfile)),
                )
                return None
            
            manager = LabelManager(params)
            ret = manager.SetPrevPoints(points2D, indexes)
            if ret:
                points3D = np.array(points3d)
                try:
                    ret = manager.ProjectCurrPoints(points3D)
                except:
                    ret = False
            if ret is False:
    
                continue
            newPoints = manager.projPoints.tolist()
            axis_points.append(newPoints)
            object_nums.append(object_id)
            
            #send to new image window, which will make 3 lines, each from origin
            #to one of the 3 point values
        
        points_to_show = []
        
        for i in range(len(axis_points)):
            o,x,y,z= axis_points[i]
            obj_num = object_nums[i]
            #For x_axis
            label = "x"
            shape_type = "linestrip"
            group_id = obj_num
            shape = Shape(
                label=label,
                shape_type=shape_type,
                group_id = group_id
            )
            shape.projected= True
            shape.addPoint(QtCore.QPointF(o[0], o[1]))
            shape.addPoint(QtCore.QPointF(x[0], x[1]))
            
            shape.line_color = QtGui.QColor(255, 0, 0)
            shape.vertex_fill_color = QtGui.QColor(255, 0, 0)
                        
            shape.close()
            points_to_show.append(shape)
            
            #For x_axis
            label = "y"
            shape_type = "linestrip"
            group_id = obj_num
            shape = Shape(
                label=label,
                shape_type=shape_type,
                group_id = group_id
            )
            shape.projected= True
            shape.addPoint(QtCore.QPointF(o[0], o[1]))
            shape.addPoint(QtCore.QPointF(y[0], y[1]))
            
            shape.line_color = QtGui.QColor(0, 255, 0)
            shape.vertex_fill_color = QtGui.QColor(0, 255, 0)
                        
            shape.close()
            points_to_show.append(shape)
            
            #For z_axis
            label = "z"
            shape_type = "linestrip"
            group_id = obj_num
            shape = Shape(
                label=label,
                shape_type=shape_type,
                group_id = group_id
            )
            shape.projected= True
            shape.addPoint(QtCore.QPointF(o[0], o[1]))
            shape.addPoint(QtCore.QPointF(z[0], z[1]))
            
            shape.line_color = QtGui.QColor(0, 0, 255)
            shape.vertex_fill_color = QtGui.QColor(0, 0, 255)
                        
            shape.close()
            points_to_show.append(shape)
            self.clear_shape(group_id)
        self.canvas.loadShapes(points_to_show, replace=False)
        self.actions.undo.setEnabled(True)


    def compute_shape(self):
        # UD check if the button is enabled
        if not self.actions.shape_3d.isChecked():
            return
#        # disable axis show
#        if not self.actions.axis_3d.isChecked():
#            self.actions.axis_3d.toggle()
        #print('UD shape')        
        
        #list of shapes:
        labelShapes         = [i.shape() for i in self.labelList]
        labels_dict_list    = []
        groups              = self.objectList.selectedItems()
        
        for i in range(len(groups)):
            #this is the object we have selected
            object_id = groups[i].data(Qt.UserRole)
            self.clear_shape(object_id)
            #create a dictionary with each label id to its point value
            points = [[shape.points[0].x(), shape.points[0].y()] for shape in labelShapes if str(shape.group_id) == object_id]
            if len(points)<= 2:
                print("Object {} has less than three points labeled".format(str(object_id)))
                self.status("Object {} has less than three points labeled".format(str(object_id)))
                continue 
            labels      = [j.label for j in labelShapes if str(j.group_id) == object_id]
            labels_dict = dict(zip(labels, points))
            
            #UD debug
            #print(labels)
            #print(points)
            
            new_points = self.projectPoints(labels, points)
            #if points were projected properly, update the labels dictionary
            if len(new_points) > 0:
#                    # UD - points outside are ok
                for point in new_points:
                    if point[0] > self.image.width() or point[1] > self.image.height() or point[0] < 0 or point[1] < 0:
                        print(str(point), " for object ", str(object_id), "wasn't found")
                        self.status("{} for object {} was outside".format(str(point), str(object_id)))
#                        continue
            else:
                #self.Print('No Completion Found for Object {}'.format(object_id))
                self.status('No Completion Found for Object {}'.format(object_id))
                continue
            
            # get the points for the labels for each face
            projected= []
            for label, point in zip( self._config.get('labels'), new_points):
                shape = dict(
                    label=label,
                    shape_type="point",
                    group_id=str(object_id),
                    points= [[point[0], point[1]]],
                    flags = {},
                    projected=True
                )
                projected.append(shape)
            labels_dict = dict(zip(self._config.get('labels'), projected))
            labels_dict_list.append(labels_dict)
            points_to_show = []
            for point in projected:
                label = point.get("label")
                shape_type = "polygon"
                group_id = point.get("group_id")
                shape = Shape(
                    label=label,
                    shape_type=shape_type,
                    group_id=group_id,
                )
                shape.point_type = shape.P_SQUARE
                shape.projected= True
                x,y = point.get('points')[0]
                shape.addPoint(QtCore.QPointF(x, y))
                
                rgb = self._get_rgb_by_object(shape.group_id) if shape.group_id is not None else self._get_rgb_by_label(
                shape.label)
    
                new_r, new_g, new_b = [255-x for x in rgb]
                shape.line_color = QtGui.QColor(new_r, new_g, new_b)
                shape.vertex_fill_color = QtGui.QColor(new_r, new_g, new_b)
                            
                shape.close()
                points_to_show.append(shape)
            self.canvas.loadShapes(points_to_show, replace=False)
            data = json.load(open(self.jsonfile, "r", encoding="utf-8"))
            json_faces = data.get("RoiFaces3D", None)
            if json_faces:
                all_faces =[]
                faces = []
                for i in range(len(labels_dict_list)):
                    labels_dict = labels_dict_list[i]
                    for face in json_faces:
                        face_points = []
                        for p in face:
                            if not isinstance(p, str):
                                print("Invalid Labels: labels aren't formatted correctly")
                                self.status("Invalid Labels: labels aren't formatted correctly")
                                return None
                            if p in labels_dict:
                                face_points.append(labels_dict[p])
                            else:
                                break
                        if len(face) == len(face_points):
                            faces.append(face_points)
                        else:
                            print('Not Enough Points Found')
                            self.status('Not enough points found')
                            continue
                    all_faces.append(faces)
                if all_faces:
                    shapes_to_show = []
                    for obj in all_faces:
                        for face in obj:
                            label = face[0].get('label')
                            
                            shape_type = "polygon"
                            group_id = face[0].get("group_id")
                
                
                
                            shape = Shape(
                                label=label,
                                shape_type=shape_type,
                                group_id=group_id,
                            )
                            
                            for d in face:
                                x,y = d.get('points')[0]
                                shape.addPoint(QtCore.QPointF(x, y))
                            shape.point_type = shape.P_SQUARE
                            shape.projected= True
                            rgb = self._get_rgb_by_object(shape.group_id) if shape.group_id is not None else self._get_rgb_by_label(
                            shape.label)
                
                            new_r, new_g, new_b = [255-x for x in rgb]
                            shape.line_color = QtGui.QColor(new_r, new_g, new_b)
                            shape.vertex_fill_color = QtGui.QColor(new_r, new_g, new_b)
                            
                            
                            shape.close()
                            shapes_to_show.append(shape)
                            
                    #show the shapes
                    self.actions.undo.setEnabled(True)
                    self.canvas.loadShapes(shapes_to_show, replace=False)
                else:
                    print("Faces not found")
                    self.status("Faces not found")
                    return None
                #otherwise ignore this face
            else:
                print("JSON file with faces isn't uploaded")
                self.status("JSON File with faces isn't uploaded")
                return None

    def clear_shape(self, obj=None):
        deleted = []
        if not obj:
            for shape in self.canvas.shapes:
                if shape.projected:
                    deleted.append(shape)
        else:
            for shape in self.canvas.shapes:
                if shape.group_id == obj and shape.projected:
                    deleted.append(shape)
        for shape in deleted:
            self.canvas.shapes.remove(shape)
        self.canvas.update()
    
    def scrollRequest(self, delta, orientation):
        units = -delta * 0.1  # natural scroll
        bar = self.scrollBars[orientation]
        value = bar.value() + bar.singleStep() * units
        self.setScroll(orientation, value)

    def setScroll(self, orientation, value):
        self.scrollBars[orientation].setValue(value)
        self.scroll_values[orientation][self.filename] = value

    def setZoom(self, value):
        self.actions.fitWidth.setChecked(False)
        self.actions.fitWindow.setChecked(False)
        self.zoomMode = self.MANUAL_ZOOM
        self.zoomWidget.setValue(value)
        self.zoom_values[self.filename] = (self.zoomMode, value)

    def addZoom(self, increment=1.1):
        zoom_value = self.zoomWidget.value() * increment
        if increment > 1:
            zoom_value = math.ceil(zoom_value)
        else:
            zoom_value = math.floor(zoom_value)
        self.setZoom(zoom_value)

    def zoomRequest(self, delta, pos):
        canvas_width_old = self.canvas.width()
        units = 1.1
        if delta < 0:
            units = 0.9
        self.addZoom(units)

        canvas_width_new = self.canvas.width()
        if canvas_width_old != canvas_width_new:
            canvas_scale_factor = canvas_width_new / canvas_width_old

            x_shift = round(pos.x() * canvas_scale_factor) - pos.x()
            y_shift = round(pos.y() * canvas_scale_factor) - pos.y()

            self.setScroll(
                Qt.Horizontal,
                self.scrollBars[Qt.Horizontal].value() + x_shift,
            )
            self.setScroll(
                Qt.Vertical,
                self.scrollBars[Qt.Vertical].value() + y_shift,
            )

    def setFitWindow(self, value=True):
        if value:
            self.actions.fitWidth.setChecked(False)
        self.zoomMode = self.FIT_WINDOW if value else self.MANUAL_ZOOM
        self.adjustScale()

    def setFitWidth(self, value=True):
        if value:
            self.actions.fitWindow.setChecked(False)
        self.zoomMode = self.FIT_WIDTH if value else self.MANUAL_ZOOM
        self.adjustScale()

    def onNewBrightnessContrast(self, qimage):
        self.canvas.loadPixmap(
            QtGui.QPixmap.fromImage(qimage), clear_shapes=False
        )

    def brightnessContrast(self, value):
        dialog = BrightnessContrastDialog(
            utils.img_data_to_pil(self.imageData),
            self.onNewBrightnessContrast,
            parent=self,
        )
        brightness, contrast = self.brightnessContrast_values.get(
            self.filename, (None, None)
        )
        if brightness is not None:
            dialog.slider_brightness.setValue(brightness)
        if contrast is not None:
            dialog.slider_contrast.setValue(contrast)
        dialog.exec_()

        brightness = dialog.slider_brightness.value()
        contrast = dialog.slider_contrast.value()
        self.brightnessContrast_values[self.filename] = (brightness, contrast)

    def togglePolygons(self, value):
        for item in self.labelList:
            item.setCheckState(Qt.Checked if value else Qt.Unchecked)

    def loadFile(self, filename=None):
        """Load the specified file, or the last opened file if None."""
        # changing fileListWidget loads file
        if filename in self.imageList and (
                self.fileListWidget.currentRow() != self.imageList.index(filename)
        ):
            self.fileListWidget.setCurrentRow(self.imageList.index(filename))
            self.fileListWidget.repaint()
            return

        self.resetState()
        self.canvas.setEnabled(False)
        if filename is None:
            filename = self.settings.value("filename", "")
        filename = str(filename)
        if not QtCore.QFile.exists(filename):
            self.errorMessage(
                self.tr("Error opening file"),
                self.tr("No such file: <b>%s</b>") % filename,
            )
            return False
        # assumes same name, but json extension
        self.status(self.tr("Loading %s...") % osp.basename(str(filename)))
        label_file = osp.splitext(filename)[0] + ".json"
        ext = osp.splitext(filename)[1]
        if ext != ".json":
            self.imageType = ext
        if self.output_dir:
            label_file_without_path = osp.basename(label_file)
            label_file = osp.join(self.output_dir, label_file_without_path)
        if QtCore.QFile.exists(label_file) and LabelFile.is_label_file(
                label_file
        ):
            try:
                self.labelFile = LabelFile(label_file)
            except LabelFileError as e:
                self.errorMessage(
                    self.tr("Error opening file"),
                    self.tr(
                        "<p><b>%s</b></p>"
                        "<p>Make sure <i>%s</i> is a valid label file."
                    )
                    % (e, label_file),
                )
                self.status(self.tr("Error reading %s") % label_file)
                return False
            self.imageData = self.labelFile.imageData
            self.imagePath = osp.join(
                osp.dirname(label_file),
                self.labelFile.imagePath,
            )
            self.otherData = self.labelFile.otherData
        else:
            self.imageData = LabelFile.load_image_file(filename)
            if self.imageData:
                self.imagePath = filename
            self.labelFile = None
        image = QtGui.QImage.fromData(self.imageData)
        size = image.size()
        Shape.image_width = size.width()
        if image.isNull():
            formats = [
                "*.{}".format(fmt.data().decode())
                for fmt in QtGui.QImageReader.supportedImageFormats()
            ]
            self.errorMessage(
                self.tr("Error opening file"),
                self.tr(
                    "<p>Make sure <i>{0}</i> is a valid image file.<br/>"
                    "Supported image formats: {1}</p>"
                ).format(filename, ",".join(formats)),
            )
            self.status(self.tr("Error reading %s") % filename)
            return False
        self.image = image
        self.filename = filename
        self.settings.setValue(
            "filename", self.filename)
        # if ext != ".json":
        #     self.lastOpenImg = filename
        #     self._config["last_open_img"] = filename
        #     self.updateConfig()
        if self._config.get("keep_prev"):
            prev_shapes = self.canvas.shapes
        self.canvas.loadPixmap(QtGui.QPixmap.fromImage(image))
        flags = {k: False for k in self._config.get("flags") or []}
        if self.labelFile:
            self.loadLabels(self.labelFile.shapes)
            if self.labelFile.flags is not None:
                flags.update(self.labelFile.flags)
            if not self.imageType:
                self.imageType = osp.splitext(self.labelFile.ImageName)[1]
        self.loadFlags(flags)
        if self._config.get("keep_prev") and self.noShapes():
            self.loadShapes(prev_shapes, replace=False)
            self.setDirty()
        else:
            self.setClean()
        self.canvas.setEnabled(True)
        # set zoom values
        is_initial_load = not self.zoom_values
        if self.filename in self.zoom_values:
            self.zoomMode = self.zoom_values[self.filename][0]
            self.setZoom(self.zoom_values[self.filename][1])
        elif is_initial_load or not self._config.get("keep_prev_scale"):
            self.adjustScale(initial=True)
        # set scroll values
        for orientation in self.scroll_values:
            if self.filename in self.scroll_values[orientation]:
                self.setScroll(
                    orientation, self.scroll_values[orientation][self.filename]
                )
        # set brightness constrast values
        dialog = BrightnessContrastDialog(
            utils.img_data_to_pil(self.imageData),
            self.onNewBrightnessContrast,
            parent=self,
        )
        brightness, contrast = self.brightnessContrast_values.get(
            self.filename, (None, None)
        )
        if self._config.get("keep_prev_brightness") and self.recentFiles:
            brightness, _ = self.brightnessContrast_values.get(
                self.recentFiles[0], (None, None)
            )
        if self._config.get("keep_prev_contrast") and self.recentFiles:
            _, contrast = self.brightnessContrast_values.get(
                self.recentFiles[0], (None, None)
            )
        if brightness is not None:
            dialog.slider_brightness.setValue(brightness)
        if contrast is not None:
            dialog.slider_contrast.setValue(contrast)
        self.brightnessContrast_values[self.filename] = (brightness, contrast)
        if brightness is not None or contrast is not None:
            dialog.onNewValue(None)
        self.paintCanvas()
        self.addRecentFile(self.filename)
        self.toggleActions(True)
        self.status(self.tr("Loaded %s") % osp.basename(str(filename)))
        return True

    def resizeEvent(self, event):
        if (
                self.canvas
                and not self.image.isNull()
                and self.zoomMode != self.MANUAL_ZOOM
        ):
            self.adjustScale()
        super(MainWindow, self).resizeEvent(event)

    def paintCanvas(self):
        assert not self.image.isNull(), "cannot paint null image"
        self.canvas.scale = 0.01 * self.zoomWidget.value()
        self.canvas.adjustSize()
        self.canvas.update()

    def adjustScale(self, initial=False):
        value = self.scalers[self.FIT_WINDOW if initial else self.zoomMode]()
        value = int(100 * value)
        self.zoomWidget.setValue(value)
        self.zoom_values[self.filename] = (self.zoomMode, value)

    def scaleFitWindow(self):
        """Figure out the size of the pixmap to fit the main widget."""
        e = 2.0  # So that no scrollbars are generated.
        w1 = self.centralWidget().width() - e
        h1 = self.centralWidget().height() - e
        a1 = w1 / h1
        # Calculate a new scale value based on the pixmap's aspect ratio.
        w2 = self.canvas.pixmap.width() - 0.0
        h2 = self.canvas.pixmap.height() - 0.0
        a2 = w2 / h2
        return w1 / w2 if a2 >= a1 else h1 / h2

    def scaleFitWidth(self):
        # The epsilon does not seem to work too well here.
        w = self.centralWidget().width() - 2.0
        return w / self.canvas.pixmap.width()

    def enableSaveImageWithData(self, enabled):
        self._config["store_data"] = enabled
        self.actions.saveWithImageData.setChecked(enabled)

    def closeEvent(self, event):
        if not self.mayContinue():
            event.ignore()
        self.settings.setValue(
            "filename", self.filename if self.filename else ""
        )
        self.settings.setValue("window/size", self.size())
        self.settings.setValue("window/position", self.pos())
        self.settings.setValue("window/state", self.saveState())
        self.settings.setValue("recentFiles", self.recentFiles)
        # ask the use for where to save the labels
        # self.settings.setValue('window/geometry', self.saveGeometry())

    def dragEnterEvent(self, event):
        extensions = [
            ".%s" % fmt.data().decode().lower()
            for fmt in QtGui.QImageReader.supportedImageFormats()
        ]
        if event.mimeData().hasUrls():
            items = [i.toLocalFile() for i in event.mimeData().urls()]
            if any([i.lower().endswith(tuple(extensions)) for i in items]):
                event.accept()
        else:
            event.ignore()

    def dropEvent(self, event):
        if not self.mayContinue():
            event.ignore()
            return
        items = [i.toLocalFile() for i in event.mimeData().urls()]
        self.importDroppedImageFiles(items)

    # User Dialogs #

    def loadRecent(self, filename):
        if self.mayContinue():
            self.loadFile(filename)


    def track(self, shapes, prev_frame):
        #if there is an exisitng json file, maybe pull up a warning?
        old_frame = self.convertQImageToMat(prev_frame)
        frame = self.convertQImageToMat(self.image)
        new_shapes = []
        for shape in shapes:
            if shape.projected:
                continue 
            x,y = shape.points[0].x(), shape.points[0].y()
            pix_num = 64
            #get new positions
            tracker = ObjectDetector.MOSSE(old_frame, (x, y, pix_num, pix_num))
            (temp_x, temp_y), temp_psr = tracker.update(frame)
            # print(temp_psr)
            if temp_psr >1.0:
                shape.popPoint()
                shape.addPoint(QtCore.QPointF(temp_x, temp_y))
                new_shapes.append(shape)
            else:
                tracker = None
        if new_shapes:
            self.loadShapes(new_shapes, replace = True)
            self.setDirty()

    def openPrevImg(self, _value=False, tracking =False):
        keep_prev = self._config.get("keep_prev")
        prev_shapes = self.canvas.shapes
        prev_frame = self.image
        if Qt.KeyboardModifiers() == (Qt.ControlModifier & Qt.ShiftModifier):
            self._config["keep_prev"] = True

        if not self.mayContinue():
            return

        if len(self.imageList) <= 0:
            return

        if self.filename is None:
            return

        currIndex = self.imageList.index(self.filename)
        if currIndex - 1 >= 0:
            filename = self.imageList[currIndex - 1]
            if filename:
                self.loadFile(filename)
            if tracking and not self.labelFile:
                self.track(prev_shapes, prev_frame)
            elif tracking and self.labelFile:
                mb = QtWidgets.QMessageBox
                msg = self.tr(
                    "Previous file already has labels. Do you want to remove old labels and add new labels?"
                )
                answer = mb.warning(self, self.tr("Attention"), msg, mb.Yes | mb.No)
                if answer == mb.Yes:
                    self.labelList.clear()
                    self.track(prev_shapes, prev_frame)
        self._config["keep_prev"] = keep_prev
        
        
    def openNextImg(self, _value=False, load=True, tracking = False):
        keep_prev = self._config.get("keep_prev")
        prev_shapes = self.canvas.shapes
        prev_frame = self.image

        if Qt.KeyboardModifiers() == (Qt.ControlModifier & Qt.ShiftModifier):
            self._config["keep_prev"] = True

        if not self.mayContinue():
            return

        if len(self.imageList) <= 0:
            return

        filename = None
        if self.filename is None:
            filename = self.imageList[0]
        else:
            currIndex = self.imageList.index(self.filename)
            if currIndex + 1 < len(self.imageList):
                filename = self.imageList[currIndex + 1]
            else:
                filename = self.imageList[-1]
        self.filename = filename
        self.settings.setValue(
            "filename", self.filename)

        if self.filename and load:
            self.loadFile(self.filename)
        if tracking and not self.labelFile:
            self.track(prev_shapes, prev_frame)
            # UD
            self.setEditMode()
        elif tracking and self.labelFile:
            mb = QtWidgets.QMessageBox
            msg = self.tr(
                "Next file already has labels. Do you want to remove old labels and add new labels?"
            )
            answer = mb.warning(self, self.tr("Attention"), msg, mb.Yes | mb.No)
            if answer == mb.Yes:
                self.labelList.clear()
                self.track(prev_shapes, prev_frame)
        self._config["keep_prev"] = keep_prev

    def loadVideo(self, filename, rate=None):
        out_dir = osp.splitext(osp.basename(filename))[0]
        created_dir = osp.join(osp.dirname(filename), out_dir)
        if not osp.exists(created_dir):
            os.mkdir(created_dir)

        reader = imageio.get_reader(filename)
        meta_data = reader.get_meta_data()
        fps = meta_data['fps']
        n_frames = meta_data['nframes']

        for i, img in tqdm.tqdm(enumerate(reader), total=n_frames):
            if rate is None or i % int(round(fps / rate)) == 0:
                imageio.imsave(osp.join(created_dir, '%08d.jpg' % i), img)
        self.importDirImages(created_dir)
        
    def kmeansVideo(self):
        videos = self.openFile(_value= True)
        numframes2pick, ok = QtWidgets.QInputDialog.getText(self, "Frame Extraction", "How many frames do you want to extract?")
        if not ok:
            return 
        output = extract_frames([videos], int(numframes2pick))
        self.importDirImages(output)
        
    def uniformVideo(self):
        videos = self.openFile(_value= True)
        numframes2pick, ok = QtWidgets.QInputDialog.getText(self, "Frame Extraction", "How many frames do you want to extract?")
        if not ok:
            return 
        output = extract_frames([videos], int(numframes2pick), algo = "uniform")
        self.importDirImages(output)

    #FIXME add self.lastOpenImg here
    def openFile(self, _value=False):
        if not self.mayContinue():
            return
        path = osp.dirname(str(self.filename)) if self.filename else "."
        if not self.filename and self.lastOpenDir:
            path = osp.dirname(str(self.lastOpenDir))
        formats = [
            "*.{}".format(fmt.data().decode())
            for fmt in QtGui.QImageReader.supportedImageFormats()
        ]
        video_exts = ["mp4","avi"]
        formats.extend(["*." + ext for ext in video_exts])
        filters = self.tr("Image & Label files (%s)") % " ".join(
            formats + ["*%s" % LabelFile.suffix]
        )
        filename = QtWidgets.QFileDialog.getOpenFileName(
            self,
            self.tr("%s - Choose Image or Label or Video file") % __appname__,
            path,
            filters,
        )
        if QT5:
            filename, _ = filename
        filename = str(filename)
        if _value:
            return filename
        if filename:
            if filename.split(".")[-1] in video_exts:
                self.loadVideo(filename)
            else:
                self.loadFile(filename)

    def loadJsonConfigFile(self, filename):
        try:
            data = json.load(open(filename, "r", encoding="utf-8"))
        except Exception as e:
            self.tr('Cannot open the JSON file may contain some syntax errors')
            self.tr('Error %s' %str(e))
            print(e)
            logger.error(
                "JSON file Syntax Error."
            )
            return
            
        if "RoiList" in data.keys():
            self.uniqLabelList.clear()
            for idx, label in enumerate(data.get("RoiList")):
                item = self.uniqLabelList.createItemFromLabel(label)
                self.uniqLabelList.addItem(item)
                self.uniqLabelList.setItemLabel(item, label)
                self.lbl2idx[label] = idx + 1
                if idx == 0:
                    self.uniqLabelList.setCurrentItem(item)
            #update the config file
            self._config['labels'] = data.get('RoiList')
            self._config['model_points'] = data.get("RoiCoord3D")
            
        else:
            logger.error(
                "JSON file Syntax Error - no element RoiList. Are you loading the correct JSON file?"
            )

    def openJSONConfig(self):
        #updates config file by setting the json file as the default
        if not self.mayContinue():
            return
        
        # select path according to the previous or by directory
        #path = osp.dirname(str(self.filename)) if self.filename else "."
        #if not self.filename and self.lastJsonDir:  # lastOpenDir:
        if self.lastJsonDir is None:
            self.lastJsonDir = self.lastOpenDir
            
        if osp.exists(self.lastJsonDir):  # lastOpenDir:
            path = self.lastJsonDir # lastOpenDir))
        else:
            if self.lastOpenDir and osp.exists(self.lastOpenDir):
                path = self.lastOpenDir
            else:
                path = osp.dirname(str(self.filename)) if self.filename else "."
            
        #print(path)
        #print(self.lastJsonDir)
        #print(self.filename)
        formats = [
            "*.json"
        ]
        filters = self.tr("JSON files (%s)") % " ".join(
            formats + ["*%s" % LabelFile.suffix]
        )
        filename = QtWidgets.QFileDialog.getOpenFileName(
            self,
            self.tr("%s - Choose JSON config file") % __appname__,
            path,
            filters,
        )
        if QT5:
            filename, _ = filename
        filename = str(filename)

        #TODO: add filename to last Open dir
        if filename:
            self.loadJsonConfigFile(filename)
            self.jsonfile = filename
            self.toggleActions()
            self._config["jsonfile"] = filename
            self.updateConfig()
            self.loadFile()
            self.lastJsonDir = os.path.split(filename)[0]

    def updateConfig(self):
            user_config_file = osp.abspath('label6d_session.json')
            try:
                with open(user_config_file, "w") as write_file:
                    json.dump(self._config, write_file, ensure_ascii=True, indent=2)
            except Exception as e:
                self.errorMessage("Failed to save config: {} because {}".format(user_config_file, e))

    def changeOutputDirDialog(self, _value=False):
        default_output_dir = self.output_dir
        if default_output_dir is None and self.filename:
            default_output_dir = osp.dirname(self.filename)
        if default_output_dir is None:
            default_output_dir = self.currentPath()

        output_dir = QtWidgets.QFileDialog.getExistingDirectory(
            self,
            self.tr("%s - Save/Load Annotations in Directory") % __appname__,
            default_output_dir,
            QtWidgets.QFileDialog.ShowDirsOnly
            | QtWidgets.QFileDialog.DontResolveSymlinks,
        )
        output_dir = str(output_dir)

        if not output_dir:
            return

        self.output_dir = output_dir

        self.statusBar().showMessage(
            self.tr("%s . Annotations will be saved/loaded in %s")
            % ("Change Annotations Dir", self.output_dir)
        )
        self.statusBar().show()

        current_filename = self.filename
        self.importDirImages(self.lastOpenDir, load=False)

        if current_filename in self.imageList:
            # retain currently selected file
            self.fileListWidget.setCurrentRow(
                self.imageList.index(current_filename)
            )
            self.fileListWidget.repaint()
            
    def listdir(self, file_extension,path='.'):
        ''' return list of files with extension 'file_extension' in folder 'path'
            not case sensitive
            example: names = listdir( ['.jpg', '.jpeg'], 'C:\\db\\' )
        '''
        if isinstance(file_extension,str):
           file_extension=[file_extension]
        b = []
        for j in range(m.size(file_extension)):
            a = [i for i in os.listdir(path) if (file_extension[j].lower() in i.lower())]
            a = [i for i in a if (file_extension[j].lower()==i[-len(file_extension[j]):].lower())]
            a = [os.path.join(path,i) for i in a if (os.path.isfile(os.path.join(path,i)))]
            b = b + a
        return b
    
    def loadParamsFromJson(self):
        "load json params"
        params = None
        if self.jsonfile:
            try:
                fid = open(self.jsonfile,'rt'); params = json.load(fid); fid.close()
            except Exception as e:
                print(e)
                self.errorMessage("JSON file not correct - check the error above",
                "No uploaded JSON File",
                )                
        else:
            print(self.jsonfile)
            self.errorMessage("JSON file is not specified",
                              "No uploaded JSON File",
            )
            
        return params
        
    
    def exportFiles(self):
        lic = self.license.Check()
        if not lic:
            mb = QtWidgets.QMessageBox
            mb.information(
                self,
                self.tr("License isn't valid"),
                self.tr("Need a valid license to export files. \
                        Please contact RobotAI for a license file"))
            return None
        if self.lastOpenDir:
            directory = self.lastOpenDir
        else:
            defaultOpenDirPath = (
                osp.dirname(self.filename) if self.filename else "."
            )

            directory = str(
                QtWidgets.QFileDialog.getExistingDirectory(
                    self,
                    self.tr("%s - Export Directory") % __appname__,
                    defaultOpenDirPath,
                    QtWidgets.QFileDialog.ShowDirsOnly
                    | QtWidgets.QFileDialog.DontResolveSymlinks,
                ))
        failed_files = []
#        if self.jsonfile:
#            fid = open(self.jsonfile,'rt'); params = json.load(fid); fid.close()
#        else:
#            self.errorMessage(
#                "JSON file not correct",
#                "No uploaded JSON File",
#            )
#            return None
        params = self.loadParamsFromJson()
        if params is None:
            return None       
        
        # dest_dir = directory + '_exported'
        # if os.path.exists(dest_dir):
        #     shutil.rmtree(dest_dir)
        # os.mkdir(dest_dir)
        for filename in self.listdir(['.json'], directory):
            #open file
            path, file = os.path.split(filename)
            print(file)
            self.status(str(file))
            with open(filename, 'r') as f:
                data = json.load(f)
            object_num = data.get('objectNum')
            height = data.get("imageHeight")
            width = data.get("imageWidth")
            data["version"] = __version__
            data["imageData"] = None
            data["imagePath"] = directory
            image_name = data.get("ImageName")
            objectInfo = data.get("objectInfo")
            shapes = data.get("shapes")
            shapes_projected = []
            curr_obj = 1
            for num in range(self._config.get("max_number_of_objects")):
                failed = False
                prev_points = [shape.get("points")[0] for shape in shapes if int(shape.get('group_id')) == num+1]
                if prev_points == []:
                    continue 
                labels = [shape.get("label") for shape in shapes if int(shape.get('group_id')) == num+1]
                # cfg = ConfigManager(osp.abspath(object_directory))
                manager = LabelManager(params)
                newPoints = self.projectPoints(labels, prev_points, manager)
                if newPoints is None:
                    return None
                if newPoints:
                    object_points =[]
                    #UD -Fix - allow points outside
                    for point in newPoints:
                        if point[0] > width or point[1] > height or point[0] < 0 or point[1] < 0:
                            print(str(point), " in Object Number ", str(num + 1), " was mapped utside")
                            #failed_files.append(file)
                            #failed = True
                            #break
                    if failed:
                        break
                    objectInfo[curr_obj-1]["pointNum"] = len(newPoints)
                    objectInfo[curr_obj-1]["objectId"] = num + 1
                    for label, point in zip(self._config.get('labels'), newPoints):
                        shape = dict(
                            label=label,
                            points = [[point[0], point[1]]],
                            shape_type="point",
                            group_id=str(num+1),
                            flags = {},
                            projected=True
                        )
                        object_points.append(shape)
                    shapes_projected.append(object_points)
                else:
                    failed = True
                    failed_files.append(file)
                if curr_obj == object_num:
                    break
                curr_obj +=1
            if file in failed_files:
                # os.remove(filename)
                print(filename)
            else:
                data['projectedShapes'] = shapes_projected
                new_file = osp.join(directory, file)
                with open(new_file, "w") as f:
                    json.dump(data, f, ensure_ascii=True, indent=2)
                # image = osp.join(path, image_name)
                # shutil.copy(image, dest_dir)
        print("Files Exported")
        self.status('Files Exported')

        if failed_files:
            mb = QtWidgets.QMessageBox
            msg = self.tr('Files exported. These files failed: "{}" ').format(failed_files)
            mb.information(
                self,
                self.tr("Files Exported"),
                msg)
            print(failed_files)
            self.status(str(failed_files))
        else:
            mb = QtWidgets.QMessageBox
            msg = self.tr('Files successfully exported.')
            mb.information(
                self,
                self.tr("Files Exported"),
                msg)

    def cleanFiles(self):
        # remove image files without labels

        if self.lastOpenDir:
            directory = self.lastOpenDir
        else:
            defaultOpenDirPath = (
                osp.dirname(self.filename) if self.filename else "."
            )

            directory = str(
                QtWidgets.QFileDialog.getExistingDirectory(
                    self,
                    self.tr("%s - Export Directory") % __appname__,
                    defaultOpenDirPath,
                    QtWidgets.QFileDialog.ShowDirsOnly
                    | QtWidgets.QFileDialog.DontResolveSymlinks,
                ))
 
        
        # dest_dir = directory + '_exported'
        # if os.path.exists(dest_dir):
        #     shutil.rmtree(dest_dir)
        # os.mkdir(dest_dir)
        self.status('Clearing directory... %s' %directory)
        for filename in self.listdir(['.jpg'], directory):
            # image files with json
            filename_json   = filename.replace('.jpg','.json')
            if os.path.isfile(filename_json):
                #print('cannot remove file %s' %filename)
                continue
            if os.path.isfile(filename):
                try:
                    os.remove(filename)
                except:
                    self.status('Cannot remove file %s' %filename)

        self.status('Non labeled jpg files are removed')
        #print('Non labeled jpg files are removed')
            
            
    def saveFile(self, _value=False):
        assert not self.image.isNull(), "cannot save empty image"
        if self.labelFile:
            # DL20180323 - overwrite when in directory
            self._saveFile(self.labelFile.filename)
        elif self.output_file:
            self._saveFile(self.output_file)
            self.close()
        else:
            self._saveFile(self.saveFileDialog())

    def saveFileAs(self, _value=False):
        assert not self.image.isNull(), "cannot save empty image"
        self._saveFile(self.saveFileDialog())

    def saveFileDialog(self):
        caption = self.tr("%s - Choose File") % __appname__
        filters = self.tr("Label files (*%s)") % LabelFile.suffix
        if self.output_dir:
            dlg = QtWidgets.QFileDialog(
                self, caption, self.output_dir, filters
            )
        else:
            dlg = QtWidgets.QFileDialog(
                self, caption, self.currentPath(), filters
            )
        dlg.setDefaultSuffix(LabelFile.suffix[1:])
        dlg.setAcceptMode(QtWidgets.QFileDialog.AcceptSave)
        dlg.setOption(QtWidgets.QFileDialog.DontConfirmOverwrite, False)
        dlg.setOption(QtWidgets.QFileDialog.DontUseNativeDialog, False)
        basename = osp.basename(osp.splitext(self.filename)[0])
        if self.output_dir:
            default_labelfile_name = osp.join(
                self.output_dir, basename + LabelFile.suffix
            )
        else:
            default_labelfile_name = osp.join(
                self.currentPath(), basename + LabelFile.suffix
            )
        filename = dlg.getSaveFileName(
            self,
            self.tr("Choose File"),
            default_labelfile_name,
            self.tr("Label files (*%s)") % LabelFile.suffix,
        )
        if isinstance(filename, tuple):
            filename, _ = filename
        return filename

    def _saveFile(self, filename):
        if filename and self.saveLabels(filename):
            self.addRecentFile(filename)
            self.setClean()

    def closeFile(self, _value=False):
        if not self.mayContinue():
            return
        self.resetState()
        self.setClean()
        self.toggleActions(False)
        self.canvas.setEnabled(False)
        self.actions.saveAs.setEnabled(False)

    def getLabelFile(self):
        if self.filename.lower().endswith(".json"):
            label_file = self.filename
        else:
            label_file = osp.splitext(self.filename)[0] + ".json"

        return label_file

    def deleteFile(self):
        mb = QtWidgets.QMessageBox
        msg = self.tr(
            "You are about to permanently delete this label file, "
            "proceed anyway?"
        )
        answer = mb.warning(self, self.tr("Attention"), msg, mb.Yes | mb.No)
        if answer != mb.Yes:
            return

        label_file = self.getLabelFile()
        if osp.exists(label_file):
            os.remove(label_file)
            logger.info("Label file is removed: {}".format(label_file))

            item = self.fileListWidget.currentItem()
            item.setCheckState(Qt.Unchecked)

            self.resetState()


    def projectPoints(self, labels, points, manager = None):
        "projected points"
        newPoints = []
        
        # check inputs
        if not isinstance(labels, list):
            self.Print('labels - Must be a list. Json configuration problem','E')
            return newPoints
        
        if not isinstance(points, list):
            self.Print('points - Must be a list. Json configuration problem','E')
            return newPoints
        
        
        params = self.loadParamsFromJson()
        if params is None:
            return newPoints
#        if self.jsonfile:
#            fid = open(self.jsonfile,'rt'); params = json.load(fid); fid.close()
#        else:
#            self.errorMessage(
#                "JSON file not correct",
#                "No uploaded JSON File",
#            )
#            return None
        # print(points)
        if manager is None:
            manager = LabelManager(params)
            
        points2D = np.array(points) #2d points on image
        try:
            indexes = np.array([int(self.lbl2idx[label]) for label in labels])
        except Exception as e:
            print(e)
            self.errorMessage(
                "JSON file is not correct",
                "Uploaded JSON file isn't correct: {}".format(osp.relpath(self.jsonfile)),
            )
            return newPoints

        ret = manager.SetPrevPoints(points2D, indexes)
        if ret:
            points3D = np.array(params.get("RoiCoord3D"))
            try:
                ret = manager.ProjectCurrPoints(points3D)
            except Exception as e:
                print(e)
                ret = False
                
        if ret is False:
            return newPoints
        
        newPoints = manager.projPoints.tolist()
        return newPoints

    # Message Dialogs. #
    def hasLabels(self):
        if self.noShapes():
            self.errorMessage(
                "No objects labeled",
                "You must label at least one object to save the file.",
            )
            return False
        return True

    def hasLabelFile(self):
        if self.filename is None:
            return False

        label_file = self.getLabelFile()
        return osp.exists(label_file)

    def mayContinue(self):
        if not self.dirty:
            return True
        mb = QtWidgets.QMessageBox
        msg = self.tr('Save annotations to "{}" before closing?').format(
            self.filename
        )
        answer = mb.question(
            self,
            self.tr("Save annotations?"),
            msg,
            mb.Save | mb.Discard | mb.Cancel,
            mb.Save,
        )
        if answer == mb.Discard:
            return True
        elif answer == mb.Save:
            self.saveFile()
            return True
        else:  # answer == mb.Cancel
            return False

    def errorMessage(self, title, message):
        return QtWidgets.QMessageBox.critical(
            self, title, "<p><b>%s</b></p>%s" % (title, message)
        )

    def currentPath(self):
        return osp.dirname(str(self.filename)) if self.filename else "."

    def toggleKeepPrevMode(self):
        self._config["keep_prev"] = not self._config.get("keep_prev")

    def deleteSelectedShape(self):
        
        self.remLabels(self.canvas.deleteSelected())
        self.setDirty()
        if self.noShapes():
            for action in self.actions.onShapesPresent:
                action.setEnabled(False)

    def copyShape(self):
        self.canvas.endMove(copy=True)
        self.labelList.clearSelection()
        for shape in self.canvas.selectedShapes:
            self.addLabel(shape, init=True)
        self.setDirty()

    def moveShape(self):
        self.canvas.endMove(copy=False)
        self.setDirty()

    def openDirDialog(self, _value=False, dirpath=None):
        if not self.mayContinue():
            return

        defaultOpenDirPath = dirpath if dirpath else "."
        if self.lastOpenDir and osp.exists(self.lastOpenDir):
            defaultOpenDirPath = self.lastOpenDir
        else:
            defaultOpenDirPath = (
                osp.dirname(self.filename) if self.filename else "."
            )

        targetDirPath = str(
            QtWidgets.QFileDialog.getExistingDirectory(
                self,
                self.tr("%s - Open Directory") % __appname__,
                defaultOpenDirPath,
                QtWidgets.QFileDialog.ShowDirsOnly
                | QtWidgets.QFileDialog.DontResolveSymlinks,
            )
        )
        self.importDirImages(targetDirPath)

    @property
    def imageList(self):
        lst = []
        for i in range(self.fileListWidget.count()):
            item = self.fileListWidget.item(i)
            lst.append(item.text())
        return lst

    def importDroppedImageFiles(self, imageFiles):
        extensions = [
            ".%s" % fmt.data().decode().lower()
            for fmt in QtGui.QImageReader.supportedImageFormats()
        ]

        self.filename = None
        for file in imageFiles:
            if file in self.imageList or not file.lower().endswith(
                    tuple(extensions)
            ):
                continue
            label_file = osp.splitext(file)[0] + ".json"
            if self.output_dir:
                label_file_without_path = osp.basename(label_file)
                label_file = osp.join(self.output_dir, label_file_without_path)
            item = QtWidgets.QListWidgetItem(file)
            item.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
            if QtCore.QFile.exists(label_file) and LabelFile.is_label_file(
                    label_file
            ):
                item.setCheckState(Qt.Checked)
            else:
                item.setCheckState(Qt.Unchecked)
            self.fileListWidget.addItem(item)

        if len(self.imageList) > 1:
            self.actions.openNextImg.setEnabled(True)
            self.actions.openPrevImg.setEnabled(True)
            self.actions.openPrevImgTrack.setEnabled(True)
            self.actions.openNextImgTrack.setEnabled(True)

        self.openNextImg()

    def importDirImages(self, dirpath, pattern=None, load=True):
        self.actions.openNextImg.setEnabled(True)
        self.actions.openPrevImg.setEnabled(True)
        self.actions.openNextImgTrack.setEnabled(True)
        self.actions.openPrevImgTrack.setEnabled(True)

        if not self.mayContinue() or not dirpath:
            return

        self.lastOpenDir = dirpath
        self.lastJsonDir = dirpath  # make JSON look in the same folder
        self._config["last_open_dir"]= dirpath
        self.updateConfig()
        self.filename = None
        self.fileListWidget.clear()
        for filename in self.scanAllImages(dirpath):
            if pattern and pattern not in filename:
                continue
            label_file = osp.splitext(filename)[0] + ".json"
            if self.output_dir:
                label_file_without_path = osp.basename(label_file)
                label_file = osp.join(self.output_dir, label_file_without_path)
            item = QtWidgets.QListWidgetItem(filename)
            item.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
            if QtCore.QFile.exists(label_file) and LabelFile.is_label_file(
                    label_file
            ):
                item.setCheckState(Qt.Checked)
            else:
                item.setCheckState(Qt.Unchecked)
            self.fileListWidget.addItem(item)
        self.openNextImg(load=load)

    def scanAllImages(self, folderPath):
        extensions = [
            ".%s" % fmt.data().decode().lower()
            for fmt in QtGui.QImageReader.supportedImageFormats()
        ]

        images = []
        for root, dirs, files in os.walk(folderPath):
            for file in files:
                if file.lower().endswith(tuple(extensions)):
                    relativePath = osp.join(root, file)
                    images.append(relativePath)
        images.sort(key=lambda x: x.lower())
        return images
    
    def Print(self, txt='',level='I'):

        if level == 'I':
            ptxt = 'I: AP: %s' % txt
            #logging.info(ptxt)
        if level == 'W':
            ptxt = 'W: AP: %s' % txt
            #logging.warning(ptxt)
        if level == 'E':
            ptxt = 'E: AP: %s' % txt
            #logging.error(ptxt)

        print(ptxt)
