package com.example.android.camera2basic;

import android.Manifest;
import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.app.DialogFragment;
import android.app.Fragment;
import android.content.Context;
import android.content.DialogInterface;
import android.content.pm.PackageManager;
import android.content.res.Configuration;
import android.graphics.ImageFormat;
import android.graphics.Matrix;
import android.graphics.Point;
import android.graphics.RectF;
import android.graphics.SurfaceTexture;
import android.hardware.GeomagneticField;
import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.hardware.camera2.CameraAccessException;
import android.hardware.camera2.CameraCaptureSession;
import android.hardware.camera2.CameraCharacteristics;
import android.hardware.camera2.CameraDevice;
import android.hardware.camera2.CameraManager;
import android.hardware.camera2.CameraMetadata;
import android.hardware.camera2.CaptureRequest;
import android.hardware.camera2.CaptureResult;
import android.hardware.camera2.TotalCaptureResult;
import android.hardware.camera2.params.StreamConfigurationMap;
import android.location.Criteria;
import android.location.Location;
import android.location.LocationListener;
import android.location.LocationManager;
import android.location.LocationProvider;
import android.media.Image;
import android.media.ImageReader;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.support.annotation.NonNull;
import android.support.v13.app.FragmentCompat;
import android.support.v4.app.ActivityCompat;
import android.support.v4.content.ContextCompat;
import android.util.Log;
import android.util.Size;
import android.util.SparseIntArray;
import android.view.LayoutInflater;
import android.view.Surface;
import android.view.TextureView;
import android.view.View;
import android.view.ViewGroup;
import android.widget.Button;
import android.widget.CheckBox;
import android.widget.EditText;
import android.widget.TextView;
import android.widget.Toast;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;

public class Camera2BasicFragment extends Fragment
        implements View.OnClickListener, FragmentCompat.OnRequestPermissionsResultCallback, SensorEventListener {

    private SensorManager mSensorManager = null;

    // angular speeds from gyro
    private float[] gyro = new float[3];

    // rotation matrix from gyro data
    private float[] gyroMatrix = new float[9];

    // orientation angles from gyro matrix
    private float[] gyroOrientation = new float[3];

    // magnetic field vector
    private float[] magnet = new float[3];

    // accelerometer vector
    private float[] accel = new float[3];

    // orientation angles from accel and magnet
    private float[] accMagOrientation = new float[3];

    // final orientation angles from sensor fusion
    private float[] fusedOrientation = new float[3];

    // accelerometer and magnetometer based rotation matrix
    private float[] rotationMatrix = new float[9];

    public static final float EPSILON = 0.000000001f;

    public static final int TIME_CONSTANT = 30;
    public static final float FILTER_COEFFICIENT = 0.98f;
    private Timer fuseTimer = new Timer();


    TextView f1, f2, f3, Result_Distance, Result_Height, Status, Result_Height2, Latitude, Longitude, Altitude;
    EditText phone_Height;
    CheckBox elevation_Checkbox;
    int id1 = 0, id2 = 0;
    float[] deg_Value = new float[3];
    int[] deg_to_Int = new int[3];
    float Fixed_Degree, Height, Distance, Toe_dist;
    int deg_Ok = 0;
    float[] Secdeg_Value = new float[3];
    int[] Secdeg_to_Int = new int[3];
    float Fixed_Degree2, obj_Height;
    int deg2_Ok = 0;
    TextView Result_Degree;
    double longitude;
    double latitude,altitude;
    Boolean b;
    float elev1=42,elev2=0;
    float elev_diff;
    char elev_Flag='N';
    /**
     * Conversion from screen rotation to JPEG orientation.
     */
    private static final SparseIntArray ORIENTATIONS = new SparseIntArray();
    private static final int REQUEST_CAMERA_PERMISSION = 1;
    private static final String FRAGMENT_DIALOG = "dialog";

    static {
        ORIENTATIONS.append(Surface.ROTATION_0, 90);
        ORIENTATIONS.append(Surface.ROTATION_90, 0);
        ORIENTATIONS.append(Surface.ROTATION_180, 270);
        ORIENTATIONS.append(Surface.ROTATION_270, 180);
    }

    /**
     * Tag for the {@link Log}.
     */
    private static final String TAG = "Camera2BasicFragment";

    /**
     * Camera state: Showing camera preview.
     */
    private static final int STATE_PREVIEW = 0;

    /**
     * Camera state: Waiting for the focus to be locked.
     */
    private static final int STATE_WAITING_LOCK = 1;

    /**
     * Camera state: Waiting for the exposure to be precapture state.
     */
    private static final int STATE_WAITING_PRECAPTURE = 2;

    /**
     * Camera state: Waiting for the exposure state to be something other than precapture.
     */
    private static final int STATE_WAITING_NON_PRECAPTURE = 3;

    /**
     * Camera state: Picture was taken.
     */
    private static final int STATE_PICTURE_TAKEN = 4;

    /**
     * Max preview width that is guaranteed by Camera2 API
     */
    private static final int MAX_PREVIEW_WIDTH = 1920;

    /**
     * Max preview height that is guaranteed by Camera2 API
     */
    private static final int MAX_PREVIEW_HEIGHT = 1080;

    /**
     * {@link TextureView.SurfaceTextureListener} handles several lifecycle events on a
     * {@link TextureView}.
     */
    private final TextureView.SurfaceTextureListener mSurfaceTextureListener
            = new TextureView.SurfaceTextureListener() {

        @Override
        public void onSurfaceTextureAvailable(SurfaceTexture texture, int width, int height) {
            openCamera(width, height);
        }

        @Override
        public void onSurfaceTextureSizeChanged(SurfaceTexture texture, int width, int height) {
            configureTransform(width, height);
        }

        @Override
        public boolean onSurfaceTextureDestroyed(SurfaceTexture texture) {
            return true;
        }

        @Override
        public void onSurfaceTextureUpdated(SurfaceTexture texture) {
        }

    };

    /**
     * ID of the current {@link CameraDevice}.
     */
    private String mCameraId;

    /**
     * An {@link AutoFitTextureView} for camera preview.
     */
    private AutoFitTextureView mTextureView;

    /**
     * A {@link CameraCaptureSession } for camera preview.
     */
    private CameraCaptureSession mCaptureSession;

    /**
     * A reference to the opened {@link CameraDevice}.
     */
    private CameraDevice mCameraDevice;

    /**
     * The {@link android.util.Size} of camera preview.
     */
    private Size mPreviewSize;

    /**
     * {@link CameraDevice.StateCallback} is called when {@link CameraDevice} changes its state.
     */
    private final CameraDevice.StateCallback mStateCallback = new CameraDevice.StateCallback() {

        @Override
        public void onOpened(@NonNull CameraDevice cameraDevice) {
            // This method is called when the camera is opened.  We start camera preview here.
            mCameraOpenCloseLock.release();
            mCameraDevice = cameraDevice;
            createCameraPreviewSession();
        }

        @Override
        public void onDisconnected(@NonNull CameraDevice cameraDevice) {
            mCameraOpenCloseLock.release();
            cameraDevice.close();
            mCameraDevice = null;
        }

        @Override
        public void onError(@NonNull CameraDevice cameraDevice, int error) {
            mCameraOpenCloseLock.release();
            cameraDevice.close();
            mCameraDevice = null;
            Activity activity = getActivity();
            if (null != activity) {
                activity.finish();
            }
        }

    };

    /**
     * An additional thread for running tasks that shouldn't block the UI.
     */
    private HandlerThread mBackgroundThread;

    /**
     * A {@link Handler} for running tasks in the background.
     */
    private Handler mBackgroundHandler;

    /**
     * An {@link ImageReader} that handles still image capture.
     */
    private ImageReader mImageReader;

    /**
     * This is the output file for our picture.
     */
    private File mFile;

    /**
     * This a callback object for the {@link ImageReader}. "onImageAvailable" will be called when a
     * still image is ready to be saved.
     */
    private final ImageReader.OnImageAvailableListener mOnImageAvailableListener
            = new ImageReader.OnImageAvailableListener() {

        @Override
        public void onImageAvailable(ImageReader reader) {
            mBackgroundHandler.post(new ImageSaver(reader.acquireNextImage(), mFile));
        }

    };

    /**
     * {@link CaptureRequest.Builder} for the camera preview
     */
    private CaptureRequest.Builder mPreviewRequestBuilder;

    /**
     * {@link CaptureRequest} generated by {@link #mPreviewRequestBuilder}
     */
    private CaptureRequest mPreviewRequest;

    /**
     * The current state of camera state for taking pictures.
     *
     * @see #mCaptureCallback
     */
    private int mState = STATE_PREVIEW;

    /**
     * A {@link Semaphore} to prevent the app from exiting before closing the camera.
     */
    private Semaphore mCameraOpenCloseLock = new Semaphore(1);

    /**
     * Whether the current camera device supports Flash or not.
     */
    private boolean mFlashSupported;

    /**
     * A {@link CameraCaptureSession.CaptureCallback} that handles events related to JPEG capture.
     */
    private CameraCaptureSession.CaptureCallback mCaptureCallback
            = new CameraCaptureSession.CaptureCallback() {

        private void process(CaptureResult result) {
            switch (mState) {
                case STATE_PREVIEW: {
                    // We have nothing to do when the camera preview is working normally.
                    break;
                }
                case STATE_WAITING_LOCK: {
                    Integer afState = result.get(CaptureResult.CONTROL_AF_STATE);
                    if (afState == null) {
                        captureStillPicture();
                    } else if (CaptureResult.CONTROL_AF_STATE_FOCUSED_LOCKED == afState ||
                            CaptureResult.CONTROL_AF_STATE_NOT_FOCUSED_LOCKED == afState) {
                        // CONTROL_AE_STATE can be null on some devices
                        Integer aeState = result.get(CaptureResult.CONTROL_AE_STATE);
                        if (aeState == null ||
                                aeState == CaptureResult.CONTROL_AE_STATE_CONVERGED) {
                            mState = STATE_PICTURE_TAKEN;
                            captureStillPicture();
                        } else {
                            runPrecaptureSequence();
                        }
                    }
                    break;
                }
                case STATE_WAITING_PRECAPTURE: {
                    // CONTROL_AE_STATE can be null on some devices
                    Integer aeState = result.get(CaptureResult.CONTROL_AE_STATE);
                    if (aeState == null ||
                            aeState == CaptureResult.CONTROL_AE_STATE_PRECAPTURE ||
                            aeState == CaptureRequest.CONTROL_AE_STATE_FLASH_REQUIRED) {
                        mState = STATE_WAITING_NON_PRECAPTURE;
                    }
                    break;
                }
                case STATE_WAITING_NON_PRECAPTURE: {
                    // CONTROL_AE_STATE can be null on some devices
                    Integer aeState = result.get(CaptureResult.CONTROL_AE_STATE);
                    if (aeState == null || aeState != CaptureResult.CONTROL_AE_STATE_PRECAPTURE) {
                        mState = STATE_PICTURE_TAKEN;
                        captureStillPicture();
                    }
                    break;
                }
            }
        }

        @Override
        public void onCaptureProgressed(@NonNull CameraCaptureSession session,
                                        @NonNull CaptureRequest request,
                                        @NonNull CaptureResult partialResult) {
            process(partialResult);
        }

        @Override
        public void onCaptureCompleted(@NonNull CameraCaptureSession session,
                                       @NonNull CaptureRequest request,
                                       @NonNull TotalCaptureResult result) {
            process(result);
        }

    };

    /**
     * Shows a {@link Toast} on the UI thread.
     *
     * @param text The message to show
     */
    private void showToast(final String text) {
        final Activity activity = getActivity();
        if (activity != null) {
            activity.runOnUiThread(new Runnable() {
                @Override
                public void run() {
                    Toast.makeText(activity, text, Toast.LENGTH_SHORT).show();
                }
            });
        }
    }

    /**
     * Given {@code choices} of {@code Size}s supported by a camera, choose the smallest one that
     * is at least as large as the respective texture view size, and that is at most as large as the
     * respective max size, and whose aspect ratio matches with the specified value. If such size
     * doesn't exist, choose the largest one that is at most as large as the respective max size,
     * and whose aspect ratio matches with the specified value.
     *
     * @param choices           The list of sizes that the camera supports for the intended output
     *                          class
     * @param textureViewWidth  The width of the texture view relative to sensor coordinate
     * @param textureViewHeight The height of the texture view relative to sensor coordinate
     * @param maxWidth          The maximum width that can be chosen
     * @param maxHeight         The maximum height that can be chosen
     * @param aspectRatio       The aspect ratio
     * @return The optimal {@code Size}, or an arbitrary one if none were big enough
     */
    private static Size chooseOptimalSize(Size[] choices, int textureViewWidth,
                                          int textureViewHeight, int maxWidth, int maxHeight, Size aspectRatio) {

        // Collect the supported resolutions that are at least as big as the preview Surface
        List<Size> bigEnough = new ArrayList<>();
        // Collect the supported resolutions that are smaller than the preview Surface
        List<Size> notBigEnough = new ArrayList<>();
        int w = aspectRatio.getWidth();
        int h = aspectRatio.getHeight();
        for (Size option : choices) {
            if (option.getWidth() <= maxWidth && option.getHeight() <= maxHeight &&
                    option.getHeight() == option.getWidth() * h / w) {
                if (option.getWidth() >= textureViewWidth &&
                        option.getHeight() >= textureViewHeight) {
                    bigEnough.add(option);
                } else {
                    notBigEnough.add(option);
                }
            }
        }

        // Pick the smallest of those big enough. If there is no one big enough, pick the
        // largest of those not big enough.
        if (bigEnough.size() > 0) {
            return Collections.min(bigEnough, new CompareSizesByArea());
        } else if (notBigEnough.size() > 0) {
            return Collections.max(notBigEnough, new CompareSizesByArea());
        } else {
            Log.e(TAG, "Couldn't find any suitable preview size");
            return choices[0];
        }
    }

    public static Camera2BasicFragment newInstance() {
        return new Camera2BasicFragment();
    }

    @Override
    public View onCreateView(LayoutInflater inflater, ViewGroup container,
                             Bundle savedInstanceState) {
        return inflater.inflate(R.layout.fragment_camera2_basic, container, false);
    }

    @Override
    public void onViewCreated(final View view, Bundle savedInstanceState) {

        view.findViewById(R.id.Tap).setOnClickListener(this);
        view.findViewById(R.id.H).setOnClickListener(this);
        view.findViewById(R.id.button_GPS).setOnClickListener(this);
        view.findViewById(R.id.info).setOnClickListener(this);
        elevation_Checkbox = (CheckBox) view.findViewById(R.id.elevation_Checkbox);
        mTextureView = (AutoFitTextureView) view.findViewById(R.id.texture);
        Result_Distance = (TextView) view.findViewById(R.id.Result_Distance);
        Result_Height = (TextView) view.findViewById(R.id.Result_Height);
        Latitude = (TextView) view.findViewById(R.id.Latitude);
        Longitude = (TextView) view.findViewById(R.id.Longitude);
        Altitude = (TextView) view.findViewById(R.id.Altitude);
        Result_Height2 = (TextView) view.findViewById(R.id.Result_Height2);
        Status = (TextView) view.findViewById(R.id.Status);
        phone_Height = (EditText) view.findViewById(R.id.phone_Height);
        Result_Degree = (TextView) view.findViewById(R.id.Result_Degree);

        gyroOrientation[0] = 0.0f;
        gyroOrientation[1] = 0.0f;
        gyroOrientation[2] = 0.0f;

        // initialise gyroMatrix with identity matrix
        gyroMatrix[0] = 1.0f;
        gyroMatrix[1] = 0.0f;
        gyroMatrix[2] = 0.0f;
        gyroMatrix[3] = 0.0f;
        gyroMatrix[4] = 1.0f;
        gyroMatrix[5] = 0.0f;
        gyroMatrix[6] = 0.0f;
        gyroMatrix[7] = 0.0f;
        gyroMatrix[8] = 1.0f;

        // get sensorManager and initialise sensor listeners
        mSensorManager = (SensorManager) getActivity().getSystemService(Context.SENSOR_SERVICE);
        initListeners();

        LocationManager locationManager = (LocationManager) getActivity().getSystemService(Context.LOCATION_SERVICE);
        LocationProvider locationProvider = locationManager.getProvider(LocationManager.GPS_PROVIDER);
        Boolean b1= locationProvider.supportsAltitude();
        LocationListener locationListener = new LocationListener() {
            @Override
            public void onLocationChanged(Location location) {
                latitude = location.getLatitude();
                longitude = location.getLongitude();
                b = location.hasAltitude();
                altitude = location.getAltitude();

            }

            @Override
            public void onStatusChanged(String provider, int status, Bundle extras) {

            }

            @Override
            public void onProviderEnabled(String provider) {

            }

            @Override
            public void onProviderDisabled(String provider) {

            }
        };
        // Register the listener with the Location Manager to receive location updates
        if (ActivityCompat.checkSelfPermission(getActivity(), Manifest.permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED && ActivityCompat.checkSelfPermission(getActivity(), Manifest.permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
            // TODO: Consider calling
            //    ActivityCompat#requestPermissions
            // here to request the missing permissions, and then overriding
            //   public void onRequestPermissionsResult(int requestCode, String[] permissions,
            //                                          int[] grantResults)
            // to handle the case where the user grants the permission. See the documentation
            // for ActivityCompat#requestPermissions for more details.
            return;
        }
        locationManager.requestLocationUpdates(LocationManager.NETWORK_PROVIDER, 0, 0, locationListener);



        // wait for one second until gyroscope and magnetometer/accelerometer
        // data is initialised then scedule the complementary filter task
        fuseTimer.scheduleAtFixedRate(new calculateFusedOrientationTask(),
                1000, TIME_CONSTANT);
    }

    private GeomagneticField getGeoMagneticField(Location location)
    {
        GeomagneticField geomagneticField = new GeomagneticField(
                (float) location.getLatitude(),
                (float) location.getLongitude(),
                (float) location.getAltitude(),
                System.currentTimeMillis());
        return geomagneticField;

    }


    @Override
    public void onActivityCreated(Bundle savedInstanceState) {
        super.onActivityCreated(savedInstanceState);
        mFile = new File(getActivity().getExternalFilesDir(null), "pic.jpg");
    }

    @Override
    public void onResume() {
        super.onResume();
        startBackgroundThread();

        // When the screen is turned off and turned back on, the SurfaceTexture is already
        // available, and "onSurfaceTextureAvailable" will not be called. In that case, we can open
        // a camera and start preview from here (otherwise, we wait until the surface is ready in
        // the SurfaceTextureListener).
        if (mTextureView.isAvailable()) {
            openCamera(mTextureView.getWidth(), mTextureView.getHeight());
        } else {
            mTextureView.setSurfaceTextureListener(mSurfaceTextureListener);
        }
    }

    @Override
    public void onPause() {
        closeCamera();
        stopBackgroundThread();
        super.onPause();
    }

    private void requestCameraPermission() {
        if (FragmentCompat.shouldShowRequestPermissionRationale(this, Manifest.permission.CAMERA)) {
            new ConfirmationDialog().show(getChildFragmentManager(), FRAGMENT_DIALOG);
        } else {
            FragmentCompat.requestPermissions(this, new String[]{Manifest.permission.CAMERA},
                    REQUEST_CAMERA_PERMISSION);
        }
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, @NonNull String[] permissions,
                                           @NonNull int[] grantResults) {
        if (requestCode == REQUEST_CAMERA_PERMISSION) {
            if (grantResults.length != 1 || grantResults[0] != PackageManager.PERMISSION_GRANTED) {
                ErrorDialog.newInstance(getString(R.string.request_permission))
                        .show(getChildFragmentManager(), FRAGMENT_DIALOG);
            }
        } else {
            super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        }
    }

    /**
     * Sets up member variables related to camera.
     *
     * @param width  The width of available size for camera preview
     * @param height The height of available size for camera preview
     */
    private void setUpCameraOutputs(int width, int height) {
        Activity activity = getActivity();
        CameraManager manager = (CameraManager) activity.getSystemService(Context.CAMERA_SERVICE);
        try {
            for (String cameraId : manager.getCameraIdList()) {
                CameraCharacteristics characteristics
                        = manager.getCameraCharacteristics(cameraId);

                // We don't use a front facing camera in this sample.
                Integer facing = characteristics.get(CameraCharacteristics.LENS_FACING);
                if (facing != null && facing == CameraCharacteristics.LENS_FACING_FRONT) {
                    continue;
                }

                StreamConfigurationMap map = characteristics.get(
                        CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP);
                if (map == null) {
                    continue;
                }

                // For still image captures, we use the largest available size.
                Size largest = Collections.max(
                        Arrays.asList(map.getOutputSizes(ImageFormat.JPEG)),
                        new CompareSizesByArea());
                mImageReader = ImageReader.newInstance(largest.getWidth(), largest.getHeight(),
                        ImageFormat.JPEG, /*maxImages*/2);
                mImageReader.setOnImageAvailableListener(
                        mOnImageAvailableListener, mBackgroundHandler);

                // Find out if we need to swap dimension to get the preview size relative to sensor
                // coordinate.
                int displayRotation = activity.getWindowManager().getDefaultDisplay().getRotation();
                int sensorOrientation =
                        characteristics.get(CameraCharacteristics.SENSOR_ORIENTATION);
                boolean swappedDimensions = false;
                switch (displayRotation) {
                    case Surface.ROTATION_0:
                    case Surface.ROTATION_180:
                        if (sensorOrientation == 90 || sensorOrientation == 270) {
                            swappedDimensions = true;
                        }
                        break;
                    case Surface.ROTATION_90:
                    case Surface.ROTATION_270:
                        if (sensorOrientation == 0 || sensorOrientation == 180) {
                            swappedDimensions = true;
                        }
                        break;
                    default:
                        Log.e(TAG, "Display rotation is invalid: " + displayRotation);
                }

                Point displaySize = new Point();
                activity.getWindowManager().getDefaultDisplay().getSize(displaySize);
                int rotatedPreviewWidth = width;
                int rotatedPreviewHeight = height;
                int maxPreviewWidth = displaySize.x;
                int maxPreviewHeight = displaySize.y;

                if (swappedDimensions) {
                    rotatedPreviewWidth = height;
                    rotatedPreviewHeight = width;
                    maxPreviewWidth = displaySize.y;
                    maxPreviewHeight = displaySize.x;
                }

                if (maxPreviewWidth > MAX_PREVIEW_WIDTH) {
                    maxPreviewWidth = MAX_PREVIEW_WIDTH;
                }

                if (maxPreviewHeight > MAX_PREVIEW_HEIGHT) {
                    maxPreviewHeight = MAX_PREVIEW_HEIGHT;
                }

                // Danger, W.R.! Attempting to use too large a preview size could  exceed the camera
                // bus' bandwidth limitation, resulting in gorgeous previews but the storage of
                // garbage capture data.
                mPreviewSize = chooseOptimalSize(map.getOutputSizes(SurfaceTexture.class),
                        rotatedPreviewWidth, rotatedPreviewHeight, maxPreviewWidth,
                        maxPreviewHeight, largest);

                // We fit the aspect ratio of TextureView to the size of preview we picked.
                int orientation = getResources().getConfiguration().orientation;
                if (orientation == Configuration.ORIENTATION_LANDSCAPE) {
                    mTextureView.setAspectRatio(
                            mPreviewSize.getWidth(), mPreviewSize.getHeight());
                } else {
                    mTextureView.setAspectRatio(
                            mPreviewSize.getHeight(), mPreviewSize.getWidth());
                }

                // Check if the flash is supported.
                Boolean available = characteristics.get(CameraCharacteristics.FLASH_INFO_AVAILABLE);
                mFlashSupported = available == null ? false : available;

                mCameraId = cameraId;
                return;
            }
        } catch (CameraAccessException e) {
            e.printStackTrace();
        } catch (NullPointerException e) {
            // Currently an NPE is thrown when the Camera2API is used but not supported on the
            // device this code runs.
            ErrorDialog.newInstance(getString(R.string.camera_error))
                    .show(getChildFragmentManager(), FRAGMENT_DIALOG);
        }
    }

    /**
     * Opens the camera specified by {@link Camera2BasicFragment#mCameraId}.
     */
    private void openCamera(int width, int height) {
        if (ContextCompat.checkSelfPermission(getActivity(), Manifest.permission.CAMERA)
                != PackageManager.PERMISSION_GRANTED) {
            requestCameraPermission();
            return;
        }
        setUpCameraOutputs(width, height);
        configureTransform(width, height);
        Activity activity = getActivity();
        CameraManager manager = (CameraManager) activity.getSystemService(Context.CAMERA_SERVICE);
        try {
            if (!mCameraOpenCloseLock.tryAcquire(2500, TimeUnit.MILLISECONDS)) {
                throw new RuntimeException("Time out waiting to lock camera opening.");
            }
            manager.openCamera(mCameraId, mStateCallback, mBackgroundHandler);
        } catch (CameraAccessException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            throw new RuntimeException("Interrupted while trying to lock camera opening.", e);
        }
    }

    /**
     * Closes the current {@link CameraDevice}.
     */
    private void closeCamera() {
        try {
            mCameraOpenCloseLock.acquire();
            if (null != mCaptureSession) {
                mCaptureSession.close();
                mCaptureSession = null;
            }
            if (null != mCameraDevice) {
                mCameraDevice.close();
                mCameraDevice = null;
            }
            if (null != mImageReader) {
                mImageReader.close();
                mImageReader = null;
            }
        } catch (InterruptedException e) {
            throw new RuntimeException("Interrupted while trying to lock camera closing.", e);
        } finally {
            mCameraOpenCloseLock.release();
        }
    }

    /**
     * Starts a background thread and its {@link Handler}.
     */
    private void startBackgroundThread() {
        mBackgroundThread = new HandlerThread("CameraBackground");
        mBackgroundThread.start();
        mBackgroundHandler = new Handler(mBackgroundThread.getLooper());
    }

    /**
     * Stops the background thread and its {@link Handler}.
     */
    private void stopBackgroundThread() {
        mBackgroundThread.quitSafely();
        try {
            mBackgroundThread.join();
            mBackgroundThread = null;
            mBackgroundHandler = null;
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    /**
     * Creates a new {@link CameraCaptureSession} for camera preview.
     */
    private void createCameraPreviewSession() {
        try {
            SurfaceTexture texture = mTextureView.getSurfaceTexture();
            assert texture != null;

            // We configure the size of default buffer to be the size of camera preview we want.
            texture.setDefaultBufferSize(mPreviewSize.getWidth(), mPreviewSize.getHeight());

            // This is the output Surface we need to start preview.
            Surface surface = new Surface(texture);

            // We set up a CaptureRequest.Builder with the output Surface.
            mPreviewRequestBuilder
                    = mCameraDevice.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW);
            mPreviewRequestBuilder.addTarget(surface);

            // Here, we create a CameraCaptureSession for camera preview.
            mCameraDevice.createCaptureSession(Arrays.asList(surface, mImageReader.getSurface()),
                    new CameraCaptureSession.StateCallback() {

                        @Override
                        public void onConfigured(@NonNull CameraCaptureSession cameraCaptureSession) {
                            // The camera is already closed
                            if (null == mCameraDevice) {
                                return;
                            }

                            // When the session is ready, we start displaying the preview.
                            mCaptureSession = cameraCaptureSession;
                            try {
                                // Auto focus should be continuous for camera preview.
                                mPreviewRequestBuilder.set(CaptureRequest.CONTROL_AF_MODE,
                                        CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_PICTURE);
                                // Flash is automatically enabled when necessary.
                                setAutoFlash(mPreviewRequestBuilder);

                                // Finally, we start displaying the camera preview.
                                mPreviewRequest = mPreviewRequestBuilder.build();
                                mCaptureSession.setRepeatingRequest(mPreviewRequest,
                                        mCaptureCallback, mBackgroundHandler);
                            } catch (CameraAccessException e) {
                                e.printStackTrace();
                            }
                        }

                        @Override
                        public void onConfigureFailed(
                                @NonNull CameraCaptureSession cameraCaptureSession) {
                            showToast("Failed");
                        }
                    }, null
            );
        } catch (CameraAccessException e) {
            e.printStackTrace();
        }
    }

    /**
     * Configures the necessary {@link android.graphics.Matrix} transformation to `mTextureView`.
     * This method should be called after the camera preview size is determined in
     * setUpCameraOutputs and also the size of `mTextureView` is fixed.
     *
     * @param viewWidth  The width of `mTextureView`
     * @param viewHeight The height of `mTextureView`
     */
    private void configureTransform(int viewWidth, int viewHeight) {
        Activity activity = getActivity();
        if (null == mTextureView || null == mPreviewSize || null == activity) {
            return;
        }
        int rotation = activity.getWindowManager().getDefaultDisplay().getRotation();
        Matrix matrix = new Matrix();
        RectF viewRect = new RectF(0, 0, viewWidth, viewHeight);
        RectF bufferRect = new RectF(0, 0, mPreviewSize.getHeight(), mPreviewSize.getWidth());
        float centerX = viewRect.centerX();
        float centerY = viewRect.centerY();
        if (Surface.ROTATION_90 == rotation || Surface.ROTATION_270 == rotation) {
            bufferRect.offset(centerX - bufferRect.centerX(), centerY - bufferRect.centerY());
            matrix.setRectToRect(viewRect, bufferRect, Matrix.ScaleToFit.FILL);
            float scale = Math.max(
                    (float) viewHeight / mPreviewSize.getHeight(),
                    (float) viewWidth / mPreviewSize.getWidth());
            matrix.postScale(scale, scale, centerX, centerY);
            matrix.postRotate(90 * (rotation - 2), centerX, centerY);
        } else if (Surface.ROTATION_180 == rotation) {
            matrix.postRotate(180, centerX, centerY);
        }
        mTextureView.setTransform(matrix);
    }

    /**
     * Initiate a still image capture.
     */
    private void takePicture() {
        lockFocus();
    }

    /**
     * Lock the focus as the first step for a still image capture.
     */
    private void lockFocus() {
        try {
            // This is how to tell the camera to lock focus.
            mPreviewRequestBuilder.set(CaptureRequest.CONTROL_AF_TRIGGER,
                    CameraMetadata.CONTROL_AF_TRIGGER_START);
            // Tell #mCaptureCallback to wait for the lock.
            mState = STATE_WAITING_LOCK;
            mCaptureSession.capture(mPreviewRequestBuilder.build(), mCaptureCallback,
                    mBackgroundHandler);
        } catch (CameraAccessException e) {
            e.printStackTrace();
        }
    }

    /**
     * Run the precapture sequence for capturing a still image. This method should be called when
     * we get a response in {@link #mCaptureCallback} from {@link #lockFocus()}.
     */
    private void runPrecaptureSequence() {
        try {
            // This is how to tell the camera to trigger.
            mPreviewRequestBuilder.set(CaptureRequest.CONTROL_AE_PRECAPTURE_TRIGGER,
                    CaptureRequest.CONTROL_AE_PRECAPTURE_TRIGGER_START);
            // Tell #mCaptureCallback to wait for the precapture sequence to be set.
            mState = STATE_WAITING_PRECAPTURE;
            mCaptureSession.capture(mPreviewRequestBuilder.build(), mCaptureCallback,
                    mBackgroundHandler);
        } catch (CameraAccessException e) {
            e.printStackTrace();
        }
    }

    /**
     * Capture a still picture. This method should be called when we get a response in
     * {@link #mCaptureCallback} from both {@link #lockFocus()}.
     */
    private void captureStillPicture() {
        try {
            final Activity activity = getActivity();
            if (null == activity || null == mCameraDevice) {
                return;
            }
            // This is the CaptureRequest.Builder that we use to take a picture.
            final CaptureRequest.Builder captureBuilder =
                    mCameraDevice.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE);
            captureBuilder.addTarget(mImageReader.getSurface());

            // Use the same AE and AF modes as the preview.
            captureBuilder.set(CaptureRequest.CONTROL_AF_MODE,
                    CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_PICTURE);
            setAutoFlash(captureBuilder);

            // Orientation
            int rotation = activity.getWindowManager().getDefaultDisplay().getRotation();
            captureBuilder.set(CaptureRequest.JPEG_ORIENTATION, ORIENTATIONS.get(rotation));

            CameraCaptureSession.CaptureCallback CaptureCallback
                    = new CameraCaptureSession.CaptureCallback() {

                @Override
                public void onCaptureCompleted(@NonNull CameraCaptureSession session,
                                               @NonNull CaptureRequest request,
                                               @NonNull TotalCaptureResult result) {
                    showToast("Saved: " + mFile);
                    Log.d(TAG, mFile.toString());
                    unlockFocus();
                }
            };

            mCaptureSession.stopRepeating();
            mCaptureSession.capture(captureBuilder.build(), CaptureCallback, null);
        } catch (CameraAccessException e) {
            e.printStackTrace();
        }
    }

    /**
     * Unlock the focus. This method should be called when still image capture sequence is
     * finished.
     */
    private void unlockFocus() {
        try {
            // Reset the auto-focus trigger
            mPreviewRequestBuilder.set(CaptureRequest.CONTROL_AF_TRIGGER,
                    CameraMetadata.CONTROL_AF_TRIGGER_CANCEL);
            setAutoFlash(mPreviewRequestBuilder);
            mCaptureSession.capture(mPreviewRequestBuilder.build(), mCaptureCallback,
                    mBackgroundHandler);
            // After this, the camera will go back to the normal state of preview.
            mState = STATE_PREVIEW;
            mCaptureSession.setRepeatingRequest(mPreviewRequest, mCaptureCallback,
                    mBackgroundHandler);
        } catch (CameraAccessException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void onClick(View view) {
        switch (view.getId()) {
            case R.id.button_GPS: {
                call_Elevation();
                break;
            }
            case R.id.Tap: {
                call_Sensor();
                break;
            }
            case R.id.H: {
                executeHeight();
                break;
            }
            case R.id.info: {
                Activity activity = getActivity();
                if (null != activity) {
                    new AlertDialog.Builder(activity)
                            .setMessage(R.string.intro_message)
                            .setPositiveButton(android.R.string.ok, null)
                            .show();
                }
                break;
            }
        }
    }

    private void call_Elevation() {
        Latitude.setText(String.valueOf(latitude));
        Longitude.setText(String.valueOf(longitude));
//        if(altitude != 0)
//        {
            Altitude.setText(String.valueOf(altitude));
//        }
    }


    private void call_Sensor() {
//        Sensor_Data s1 = new Sensor_Data();
//        Result.setText(deg_Calc());
        executeTap();

    }

    private void setAutoFlash(CaptureRequest.Builder requestBuilder) {
        if (mFlashSupported) {
            requestBuilder.set(CaptureRequest.CONTROL_AE_MODE,
                    CaptureRequest.CONTROL_AE_MODE_ON_AUTO_FLASH);
        }
    }


    /**
     * Saves a JPEG {@link Image} into the specified {@link File}.
     */
    private static class ImageSaver implements Runnable {

        /**
         * The JPEG image
         */
        private final Image mImage;
        /**
         * The file we save the image into.
         */
        private final File mFile;

        public ImageSaver(Image image, File file) {
            mImage = image;
            mFile = file;
        }

        @Override
        public void run() {
            ByteBuffer buffer = mImage.getPlanes()[0].getBuffer();
            byte[] bytes = new byte[buffer.remaining()];
            buffer.get(bytes);
            FileOutputStream output = null;
            try {
                output = new FileOutputStream(mFile);
                output.write(bytes);
            } catch (IOException e) {
                e.printStackTrace();
            } finally {
                mImage.close();
                if (null != output) {
                    try {
                        output.close();
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                }
            }
        }

    }

    /**
     * Compares two {@code Size}s based on their areas.
     */
    static class CompareSizesByArea implements Comparator<Size> {

        @Override
        public int compare(Size lhs, Size rhs) {
            // We cast here to ensure the multiplications won't overflow
            return Long.signum((long) lhs.getWidth() * lhs.getHeight() -
                    (long) rhs.getWidth() * rhs.getHeight());
        }

    }

    /**
     * Shows an error message dialog.
     */
    public static class ErrorDialog extends DialogFragment {

        private static final String ARG_MESSAGE = "message";

        public static ErrorDialog newInstance(String message) {
            ErrorDialog dialog = new ErrorDialog();
            Bundle args = new Bundle();
            args.putString(ARG_MESSAGE, message);
            dialog.setArguments(args);
            return dialog;
        }

        @Override
        public Dialog onCreateDialog(Bundle savedInstanceState) {
            final Activity activity = getActivity();
            return new AlertDialog.Builder(activity)
                    .setMessage(getArguments().getString(ARG_MESSAGE))
                    .setPositiveButton(android.R.string.ok, new DialogInterface.OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialogInterface, int i) {
                            activity.finish();
                        }
                    })
                    .create();
        }

    }

    /**
     * Shows OK/Cancel confirmation dialog about camera permission.
     */
    public static class ConfirmationDialog extends DialogFragment {

        @Override
        public Dialog onCreateDialog(Bundle savedInstanceState) {
            final Fragment parent = getParentFragment();
            return new AlertDialog.Builder(getActivity())
                    .setMessage(R.string.request_permission)
                    .setPositiveButton(android.R.string.ok, new DialogInterface.OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            FragmentCompat.requestPermissions(parent,
                                    new String[]{Manifest.permission.CAMERA},
                                    REQUEST_CAMERA_PERMISSION);
                        }
                    })
                    .setNegativeButton(android.R.string.cancel,
                            new DialogInterface.OnClickListener() {
                                @Override
                                public void onClick(DialogInterface dialog, int which) {
                                    Activity activity = parent.getActivity();
                                    if (activity != null) {
                                        activity.finish();
                                    }
                                }
                            })
                    .create();
        }
    }


    @Override
    public void onSensorChanged(SensorEvent event) {
        switch(event.sensor.getType()) {
            case Sensor.TYPE_ACCELEROMETER:
                // copy new accelerometer data into accel array
                // then calculate new orientation
                System.arraycopy(event.values, 0, accel, 0, 3);
                calculateAccMagOrientation();
                break;

            case Sensor.TYPE_GYROSCOPE:
                // process gyro data
                gyroFunction(event);
                break;

            case Sensor.TYPE_MAGNETIC_FIELD:
                // copy new magnetometer data into magnet array
                System.arraycopy(event.values, 0, magnet, 0, 3);
                break;
        }


    }

    @Override
    public void onAccuracyChanged(Sensor sensor, int accuracy) {

    }

    public void initListeners(){
        mSensorManager.registerListener(this,
                mSensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER),
                SensorManager.SENSOR_DELAY_FASTEST);

        mSensorManager.registerListener(this,
                mSensorManager.getDefaultSensor(Sensor.TYPE_GYROSCOPE),
                SensorManager.SENSOR_DELAY_FASTEST);

        mSensorManager.registerListener(this,
                mSensorManager.getDefaultSensor(Sensor.TYPE_MAGNETIC_FIELD),
                SensorManager.SENSOR_DELAY_FASTEST);
    }

    public void calculateAccMagOrientation() {
        if(SensorManager.getRotationMatrix(rotationMatrix, null, accel, magnet)) {
            SensorManager.getOrientation(rotationMatrix, accMagOrientation);
        }
    }

    private void getRotationVectorFromGyro(float[] gyroValues,
                                           float[] deltaRotationVector,
                                           float timeFactor)
    {
        float[] normValues = new float[3];

        // Calculate the angular speed of the sample
        float omegaMagnitude =
                (float)Math.sqrt(gyroValues[0] * gyroValues[0] +
                        gyroValues[1] * gyroValues[1] +
                        gyroValues[2] * gyroValues[2]);

        // Normalize the rotation vector if it's big enough to get the axis
        if(omegaMagnitude > EPSILON) {
            normValues[0] = gyroValues[0] / omegaMagnitude;
            normValues[1] = gyroValues[1] / omegaMagnitude;
            normValues[2] = gyroValues[2] / omegaMagnitude;
        }

        // Integrate around this axis with the angular speed by the timestep
        // in order to get a delta rotation from this sample over the timestep
        // We will convert this axis-angle representation of the delta rotation
        // into a quaternion before turning it into the rotation matrix.
        float thetaOverTwo = omegaMagnitude * timeFactor;
        float sinThetaOverTwo = (float)Math.sin(thetaOverTwo);
        float cosThetaOverTwo = (float)Math.cos(thetaOverTwo);
        deltaRotationVector[0] = sinThetaOverTwo * normValues[0];
        deltaRotationVector[1] = sinThetaOverTwo * normValues[1];
        deltaRotationVector[2] = sinThetaOverTwo * normValues[2];
        deltaRotationVector[3] = cosThetaOverTwo;
    }

    private static final float NS2S = 1.0f / 1000000000.0f;
    private float timestamp;
    private boolean initState = true;

    public void gyroFunction(SensorEvent event) {
        // don't start until first accelerometer/magnetometer orientation has been acquired
        if (accMagOrientation == null)
            return;

        // initialisation of the gyroscope based rotation matrix
        if(initState) {
            float[] initMatrix = new float[9];
            initMatrix = getRotationMatrixFromOrientation(accMagOrientation);
            float[] test = new float[3];
            SensorManager.getOrientation(initMatrix, test);
            gyroMatrix = matrixMultiplication(gyroMatrix, initMatrix);
            initState = false;
        }

        // copy the new gyro values into the gyro array
        // convert the raw gyro data into a rotation vector
        float[] deltaVector = new float[4];
        if(timestamp != 0) {
            final float dT = (event.timestamp - timestamp) * NS2S;
            System.arraycopy(event.values, 0, gyro, 0, 3);
            getRotationVectorFromGyro(gyro, deltaVector, dT / 2.0f);
        }

        // measurement done, save current time for next interval
        timestamp = event.timestamp;

        // convert rotation vector into rotation matrix
        float[] deltaMatrix = new float[9];
        SensorManager.getRotationMatrixFromVector(deltaMatrix, deltaVector);

        // apply the new rotation interval on the gyroscope based rotation matrix
        gyroMatrix = matrixMultiplication(gyroMatrix, deltaMatrix);

        // get the gyroscope based orientation from the rotation matrix
        SensorManager.getOrientation(gyroMatrix, gyroOrientation);
    }

    private float[] getRotationMatrixFromOrientation(float[] o) {
        float[] xM = new float[9];
        float[] yM = new float[9];
        float[] zM = new float[9];

        float sinX = (float)Math.sin(o[1]);
        float cosX = (float)Math.cos(o[1]);
        float sinY = (float)Math.sin(o[2]);
        float cosY = (float)Math.cos(o[2]);
        float sinZ = (float)Math.sin(o[0]);
        float cosZ = (float)Math.cos(o[0]);

        // rotation about x-axis (pitch)
        xM[0] = 1.0f; xM[1] = 0.0f; xM[2] = 0.0f;
        xM[3] = 0.0f; xM[4] = cosX; xM[5] = sinX;
        xM[6] = 0.0f; xM[7] = -sinX; xM[8] = cosX;

        // rotation about y-axis (roll)
        yM[0] = cosY; yM[1] = 0.0f; yM[2] = sinY;
        yM[3] = 0.0f; yM[4] = 1.0f; yM[5] = 0.0f;
        yM[6] = -sinY; yM[7] = 0.0f; yM[8] = cosY;

        // rotation about z-axis (azimuth)
        zM[0] = cosZ; zM[1] = sinZ; zM[2] = 0.0f;
        zM[3] = -sinZ; zM[4] = cosZ; zM[5] = 0.0f;
        zM[6] = 0.0f; zM[7] = 0.0f; zM[8] = 1.0f;

        // rotation order is y, x, z (roll, pitch, azimuth)
        float[] resultMatrix = matrixMultiplication(xM, yM);
        resultMatrix = matrixMultiplication(zM, resultMatrix);
        return resultMatrix;
    }

    private float[] matrixMultiplication(float[] A, float[] B) {
        float[] result = new float[9];

        result[0] = A[0] * B[0] + A[1] * B[3] + A[2] * B[6];
        result[1] = A[0] * B[1] + A[1] * B[4] + A[2] * B[7];
        result[2] = A[0] * B[2] + A[1] * B[5] + A[2] * B[8];

        result[3] = A[3] * B[0] + A[4] * B[3] + A[5] * B[6];
        result[4] = A[3] * B[1] + A[4] * B[4] + A[5] * B[7];
        result[5] = A[3] * B[2] + A[4] * B[5] + A[5] * B[8];

        result[6] = A[6] * B[0] + A[7] * B[3] + A[8] * B[6];
        result[7] = A[6] * B[1] + A[7] * B[4] + A[8] * B[7];
        result[8] = A[6] * B[2] + A[7] * B[5] + A[8] * B[8];

        return result;
    }




    class calculateFusedOrientationTask extends TimerTask {
        public void run() {
            float oneMinusCoeff = 1.0f - FILTER_COEFFICIENT;
            fusedOrientation[0] =
                    FILTER_COEFFICIENT * gyroOrientation[0]
                            + oneMinusCoeff * accMagOrientation[0];

            fusedOrientation[1] =
                    FILTER_COEFFICIENT * gyroOrientation[1]
                            + oneMinusCoeff * accMagOrientation[1];

            fusedOrientation[2] =
                    FILTER_COEFFICIENT * gyroOrientation[2]
                            + oneMinusCoeff * accMagOrientation[2];

            // overwrite gyro matrix and orientation with fused orientation
            // to comensate gyro drift
            gyroMatrix = getRotationMatrixFromOrientation(fusedOrientation);
            System.arraycopy(fusedOrientation, 0, gyroOrientation, 0, 3);
        }
    }

    public void executeTap() {

        //Logic to see if the user moved the hand while while fixing the Angle
        deg_Value[id1] = (float) (fusedOrientation[1] * 180 / Math.PI);
        deg_to_Int[id1] = (int) deg_Value[id1];
        id1 = id1 + 1;
        switch(id1){
            case 1:{
                //Elevation condition Check **************
                if(elevation_Checkbox.isChecked()){
                    elev_diff = elev1 - elev2;
                    elev_Flag = 'Y';
                }
                else {
                    elev_Flag = 'N';
                }

                Status.setText("Tap two more times!");
                break;
            }
            case 2:{
                Status.setText("Tap one more time!");
                break;
            }
            case 3:{
                if (deg_to_Int[0] == deg_to_Int[1] && deg_to_Int[0] == deg_to_Int[2]) {
                    Status.setText("Done");
                    deg_Ok = 1;
                    Fixed_Degree = (deg_Value[0] + deg_Value[1] + deg_Value[2]) / 3;
                    Result_Degree.setText(String.valueOf(Fixed_Degree));
                    id1 = 0;
                } else {
                    Status.setText("Moved. Tap three times again");
                    id1 = 0;
                    deg_Ok = 0;
                }
            }
        }

        //Distance Calculation from Angle of inclination
        //Formula Distance = Tan(theta) * Height;
        if (deg_Ok == 1) {
            if (Fixed_Degree < 0) {
                Fixed_Degree = Fixed_Degree * -1;
            }
//            Height Approximation logic
//            String Height1= phone_Height.getText().toString();
//            Height = Float.parseFloat(Height1);

            if(Fixed_Degree <= 35.9) Height=122;
            else if(Fixed_Degree>35.9 && Fixed_Degree<=38.5) Height= (float) 122.5;
            else if(Fixed_Degree>38.5 && Fixed_Degree<=41) Height= (float) 122.8;
            else if(Fixed_Degree>41 && Fixed_Degree<=42.5) Height= (float) 126;
            else if(Fixed_Degree>42.5 && Fixed_Degree<=43.7) Height= (float) 128.1;
            else if(Fixed_Degree>43.7 && Fixed_Degree<=45.8) Height= (float) 127.8;
            else if(Fixed_Degree>45.8 && Fixed_Degree<=48.4) Height= (float) 130;
            else if(Fixed_Degree>48.4 && Fixed_Degree<=49.6) Height= (float) 133.1;
            else if(Fixed_Degree>49.6 && Fixed_Degree<=50.7) Height= (float) 133.5;
            else if(Fixed_Degree>50.7 && Fixed_Degree<=52.5) Height= (float) 135.2;
            else if(Fixed_Degree>52.5 && Fixed_Degree<=54.7) Height= (float) 136.2;
            else if(Fixed_Degree>54.7 && Fixed_Degree<=55.8) Height= (float) 137.5;
            else if(Fixed_Degree>55.8 && Fixed_Degree<=57.6) Height= (float) 138.5;
            else if(Fixed_Degree>57.6 && Fixed_Degree<=58.4) Height= (float) 139.1;
            else if(Fixed_Degree>58.4 && Fixed_Degree<=59.7) Height= (float) 143;
            else if(Fixed_Degree>59.7 && Fixed_Degree<=61.9) Height= (float) 142.2;
            else if(Fixed_Degree>61.9 && Fixed_Degree<=62.2) Height= (float) 144.4;
            else if(Fixed_Degree>62.2 && Fixed_Degree<=62.6) Height= (float) 144.1;
            else if(Fixed_Degree>62.6 && Fixed_Degree<=63.5) Height= (float) 153;
            else if(Fixed_Degree>63.5 && Fixed_Degree<=64.2) Height= (float) 144.5;
            else if(Fixed_Degree>64.2 && Fixed_Degree<=65.5) Height= (float) 142.5;
            else if(Fixed_Degree>65.5 && Fixed_Degree<=65.8) Height= (float) 145.8;
            else if(Fixed_Degree>65.8 && Fixed_Degree<=66.7) Height= (float) 146.2;
            else if(Fixed_Degree>66.7 && Fixed_Degree<=66.8) Height= (float) 148;
            else if(Fixed_Degree>66.8 && Fixed_Degree<=67.6) Height= (float) 147.5;
            else if(Fixed_Degree>67.6 && Fixed_Degree<=67.8) Height= (float) 146.2;


            //Default Height Value
            if(Height>0){}
            else {
                Height=130;
            }
            //Toe Distance
            Toe_dist=(float) 19.3;

            //Elevation condition
            if(elev_Flag=='Y'){
            Height = Height+ elev_diff;
            elev_Flag = 'N';
            }

            Distance = (float) (Math.tan(Double.valueOf(Fixed_Degree*0.0174533)) * Height);
            Distance = Distance + Toe_dist;
            Result_Distance.setText(String.valueOf(Distance));
        }
    }
    public void executeHeight() {

        //Logic to see if the user moved the hand while while fixing the Angle
        Secdeg_Value[id2] = (float) (fusedOrientation[1] * 180 / Math.PI);
        Secdeg_to_Int[id2] = (int) Secdeg_Value[id2];
        id2 = id2 + 1;
        switch (id2) {
            case 1: {
                Status.setText("Tap two more times!");
                break;
            }
            case 2: {
                Status.setText("Tap one more time!");
                break;
            }
            case 3: {
                if (Secdeg_to_Int[0] == Secdeg_to_Int[1] && Secdeg_to_Int[0] == Secdeg_to_Int[2]) {
                    Status.setText("Height is calculated");
                    deg2_Ok = 1;
                    Fixed_Degree2 = (Secdeg_Value[0] + Secdeg_Value[1] + Secdeg_Value[2]) / 3;
                    Result_Degree.setText(String.valueOf(Fixed_Degree2));
                    id2 = 0;
                } else {
                    Status.setText("2nd degree Moved.Tap 3 times");
                    id2 = 0;
                    deg2_Ok = 0;
                }
            }
        }

        //Height calculation part once degree fixed:
        if (deg2_Ok == 1) {
            if (Fixed_Degree2 < 0) {
                Fixed_Degree2 = Fixed_Degree2 * -1;
            }
            float tan_Theta = (float) (Math.tan(Double.valueOf(Fixed_Degree2 * 0.0174533)));

            //a1 is Height. Dist/Tan theta
            float a1 = (Distance - Toe_dist) / tan_Theta;
            obj_Height = Height - a1;

            float tmp_Ht = obj_Height;
            Result_Height2.setText(String.valueOf(tmp_Ht));

            float uncal_Obj_Height=obj_Height;

            //Calibrate Height
            if(!((Distance<=75 && Fixed_Degree2 <=40.2) ||
                    (Distance>75 && Distance<=105 && Fixed_Degree2 >40.2 && Fixed_Degree2 <=49.1) ||
                    (Distance>105 && Distance<=135 && Fixed_Degree2 >49.1 && Fixed_Degree2 <=56.3) ||
                    (Distance>135 && Distance<=165 && Fixed_Degree2 >56.3 && Fixed_Degree2 <=60.4))) {

                if (Distance <= 70) {
                    if (Fixed_Degree2 <= 32.8) obj_Height = (float) (obj_Height + 4.1);
                    else if (Fixed_Degree2 > 32.8 && Fixed_Degree2 <= 35.78)
                        obj_Height = (float) (obj_Height + 6.04);
                    else if (Fixed_Degree2 > 35.78 && Fixed_Degree2 <= 38.76)
                        obj_Height = (float) (obj_Height + 7.98);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 38.76 && Fixed_Degree2 <= 41.74)
                        obj_Height = (float) (obj_Height + 9.92);
                    else if (Fixed_Degree2 > 41.74 && Fixed_Degree2 <= 44.72)
                        obj_Height = (float) (obj_Height + 11.86);
                    else if (Fixed_Degree2 > 44.72 && Fixed_Degree2 <= 47.7)
                        obj_Height = (float) (obj_Height + 13.8);
                    else if (Fixed_Degree2 > 44.7 && Fixed_Degree2 <= 52.5)
                        obj_Height = (float) (obj_Height + 16.84); // Modified
                    else if (Fixed_Degree2 > 52.5 && Fixed_Degree2 <= 57.3)
                        obj_Height = (float) (obj_Height + 19.88);
                    else if (Fixed_Degree2 > 57.3 && Fixed_Degree2 <= 62.1)
                        obj_Height = (float) (obj_Height + 22.92);
                    else if (Fixed_Degree2 > 62.1 && Fixed_Degree2 <= 66.9)
                        obj_Height = (float) (obj_Height + 25.96);
                    else if (Fixed_Degree2 > 66.9 && Fixed_Degree2 <= 71.7)
                        obj_Height = (float) (obj_Height + 29);
                    else if (Fixed_Degree2 > 71.7) obj_Height = (float) (obj_Height + 30);
                } else if (Distance > 70 && Distance <= 100) {
                    if (Fixed_Degree2 <= 41.1) obj_Height = (float) (obj_Height + 4.2);
                    else if (Fixed_Degree2 > 41.1 && Fixed_Degree2 <= 44.3)
                        obj_Height = (float) (obj_Height + 5.64);
                    else if (Fixed_Degree2 > 44.3 && Fixed_Degree2 <= 47.5)
                        obj_Height = (float) (obj_Height + 7.08);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 47.5 && Fixed_Degree2 <= 50.7)
                        obj_Height = (float) (obj_Height + 8.52);
                    else if (Fixed_Degree2 > 50.7 && Fixed_Degree2 <= 53.9)
                        obj_Height = (float) (obj_Height + 9.96);
                    else if (Fixed_Degree2 > 53.9 && Fixed_Degree2 <= 57.1)
                        obj_Height = (float) (obj_Height + 11.4);
                    else if (Fixed_Degree2 > 57.1 && Fixed_Degree2 <= 61.04)
                        obj_Height = (float) (obj_Height + 13.88); // Modified
                    else if (Fixed_Degree2 > 61.04 && Fixed_Degree2 <= 64.98)
                        obj_Height = (float) (obj_Height + 16.36);
                    else if (Fixed_Degree2 > 64.98 && Fixed_Degree2 <= 68.92)
                        obj_Height = (float) (obj_Height + 18.84);
                    else if (Fixed_Degree2 > 68.92 && Fixed_Degree2 <= 72.86)
                        obj_Height = (float) (obj_Height + 21.32);
                    else if (Fixed_Degree2 > 72.86 && Fixed_Degree2 <= 76.8)
                        obj_Height = (float) (obj_Height + 23.8);
                    else if (Fixed_Degree2 > 76.8) obj_Height = (float) (obj_Height + 25);
                } else if (Distance > 100 && Distance <= 130) {
                    if (Fixed_Degree2 <= 49.8) obj_Height = (float) (obj_Height + 3);
                    else if (Fixed_Degree2 > 49.8 && Fixed_Degree2 <= 52.36)
                        obj_Height = (float) (obj_Height + 4.56);
                    else if (Fixed_Degree2 > 52.36 && Fixed_Degree2 <= 54.92)
                        obj_Height = (float) (obj_Height + 6.12);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 54.92 && Fixed_Degree2 <= 57.48)
                        obj_Height = (float) (obj_Height + 7.68);
                    else if (Fixed_Degree2 > 57.48 && Fixed_Degree2 <= 60.04)
                        obj_Height = (float) (obj_Height + 9.24);
                    else if (Fixed_Degree2 > 60.04 && Fixed_Degree2 <= 62.6)
                        obj_Height = (float) (obj_Height + 10.8);
                    else if (Fixed_Degree2 > 62.6 && Fixed_Degree2 <= 65.96)
                        obj_Height = (float) (obj_Height + 12.82); // Modified
                    else if (Fixed_Degree2 > 65.96 && Fixed_Degree2 <= 69.32)
                        obj_Height = (float) (obj_Height + 14.84);
                    else if (Fixed_Degree2 > 69.32 && Fixed_Degree2 <= 72.68)
                        obj_Height = (float) (obj_Height + 16.86);
                    else if (Fixed_Degree2 > 72.68 && Fixed_Degree2 <= 76.04)
                        obj_Height = (float) (obj_Height + 18.88);
                    else if (Fixed_Degree2 > 76.04 && Fixed_Degree2 <= 79.4)
                        obj_Height = (float) (obj_Height + 20.9);
                    else if (Fixed_Degree2 > 79.4) obj_Height = (float) (obj_Height + 22);
                } else if (Distance > 130 && Distance <= 160) {
                    if (Fixed_Degree2 <= 54.2) obj_Height = (float) (obj_Height + 2.5);
                    else if (Fixed_Degree2 > 54.2 && Fixed_Degree2 <= 56.8)
                        obj_Height = (float) (obj_Height + 5.5);
                    else if (Fixed_Degree2 > 56.8 && Fixed_Degree2 <= 59.2)
                        obj_Height = (float) (obj_Height + 6);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 59.2 && Fixed_Degree2 <= 61.5)
                        obj_Height = (float) (obj_Height + 9);
                    else if (Fixed_Degree2 > 61.5 && Fixed_Degree2 <= 65.4)
                        obj_Height = (float) (obj_Height + 9.5);
                    else if (Fixed_Degree2 > 65.4 && Fixed_Degree2 <= 67.1)
                        obj_Height = (float) (obj_Height + 11.5);
                    else if (Fixed_Degree2 > 67.1 && Fixed_Degree2 <= 70.2)
                        obj_Height = (float) (obj_Height + 12); // Modified
                    else if (Fixed_Degree2 > 70.2 && Fixed_Degree2 <= 72.4)
                        obj_Height = (float) (obj_Height + 14);
                    else if (Fixed_Degree2 > 72.4 && Fixed_Degree2 <= 75.4)
                        obj_Height = (float) (obj_Height + 15.5);
                    else if (Fixed_Degree2 > 75.4 && Fixed_Degree2 <= 78.2)
                        obj_Height = (float) (obj_Height + 17);
                    else if (Fixed_Degree2 > 78.2 && Fixed_Degree2 <= 80.6)
                        obj_Height = (float) (obj_Height + 20);
                    else if (Fixed_Degree2 > 80.6) obj_Height = (float) (obj_Height + 23);
                }else if (Distance > 160 && Distance <= 190) {
                    if (Fixed_Degree2 <= 58.5) obj_Height = (float) (obj_Height + 4.8);
                    else if (Fixed_Degree2 > 58.5 && Fixed_Degree2 <= 60.6)
                        obj_Height = (float) (obj_Height + 6.64);
                    else if (Fixed_Degree2 > 60.6 && Fixed_Degree2 <= 62.7)
                        obj_Height = (float) (obj_Height + 8.48);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 62.7 && Fixed_Degree2 <= 64.8)
                        obj_Height = (float) (obj_Height + 10.32);
                    else if (Fixed_Degree2 > 64.8 && Fixed_Degree2 <= 66.9)
                        obj_Height = (float) (obj_Height + 12.16);
                    else if (Fixed_Degree2 > 66.9 && Fixed_Degree2 <= 69)
                        obj_Height = (float) (obj_Height + 14);
                    else if (Fixed_Degree2 > 69 && Fixed_Degree2 <= 71.68)
                        obj_Height = (float) (obj_Height + 15.38); // Modified
                    else if (Fixed_Degree2 > 71.68 && Fixed_Degree2 <= 74.36)
                        obj_Height = (float) (obj_Height + 16.76);
                    else if (Fixed_Degree2 > 74.36 && Fixed_Degree2 <= 77.04)
                        obj_Height = (float) (obj_Height + 18.14);
                    else if (Fixed_Degree2 > 77.04 && Fixed_Degree2 <= 79.72)
                        obj_Height = (float) (obj_Height + 19.52);
                    else if (Fixed_Degree2 > 79.72 && Fixed_Degree2 <= 82.4)
                        obj_Height = (float) (obj_Height + 20.9);
                    else if (Fixed_Degree2 > 82.4) obj_Height = (float) (obj_Height + 22.3);
                }
                else if (Distance > 190 && Distance <= 220) {
                    if (Fixed_Degree2 <= 62.2) obj_Height = (float) (obj_Height + 1.7);
                    else if (Fixed_Degree2 > 62.2 && Fixed_Degree2 <= 64.26)
                        obj_Height = (float) (obj_Height + 2.84);
                    else if (Fixed_Degree2 > 64.26 && Fixed_Degree2 <= 66.32)
                        obj_Height = (float) (obj_Height + 3.98);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 66.32 && Fixed_Degree2 <= 68.38)
                        obj_Height = (float) (obj_Height + 5.12);
                    else if (Fixed_Degree2 > 68.38 && Fixed_Degree2 <= 70.44)
                        obj_Height = (float) (obj_Height + 6.26);
                    else if (Fixed_Degree2 > 70.44 && Fixed_Degree2 <= 72.5)
                        obj_Height = (float) (obj_Height + 7.4);
                    else if (Fixed_Degree2 > 72.5 && Fixed_Degree2 <= 74.68)
                        obj_Height = (float) (obj_Height + 9.2); // Modified
                    else if (Fixed_Degree2 > 74.68 && Fixed_Degree2 <= 76.86)
                        obj_Height = (float) (obj_Height + 11);
                    else if (Fixed_Degree2 > 76.86 && Fixed_Degree2 <= 79.04)
                        obj_Height = (float) (obj_Height + 12.8);
                    else if (Fixed_Degree2 > 79.04 && Fixed_Degree2 <= 81.22)
                        obj_Height = (float) (obj_Height + 14.6);
                    else if (Fixed_Degree2 > 81.22 && Fixed_Degree2 <= 83.4)
                        obj_Height = (float) (obj_Height + 16.4);
                    else if (Fixed_Degree2 > 83.4) obj_Height = (float) (obj_Height + 18.4);
                }
                else if (Distance > 220 && Distance <= 250) {
                    if (Fixed_Degree2 <= 64.8) obj_Height = (float) (obj_Height + 7.6);
                    else if (Fixed_Degree2 > 64.8 && Fixed_Degree2 <= 66.7)
                        obj_Height = (float) (obj_Height + 8.28);
                    else if (Fixed_Degree2 > 66.7 && Fixed_Degree2 <= 68.6)
                        obj_Height = (float) (obj_Height + 8.96);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 68.6 && Fixed_Degree2 <= 70.5)
                        obj_Height = (float) (obj_Height + 9.64);
                    else if (Fixed_Degree2 > 70.5 && Fixed_Degree2 <= 72.4)
                        obj_Height = (float) (obj_Height + 10.32);
                    else if (Fixed_Degree2 > 72.4 && Fixed_Degree2 <= 74.3)
                        obj_Height = (float) (obj_Height + 11);
                    else if (Fixed_Degree2 > 74.3 && Fixed_Degree2 <= 76.28)
                        obj_Height = (float) (obj_Height + 12.14); // Modified
                    else if (Fixed_Degree2 > 76.28 && Fixed_Degree2 <= 78.26)
                        obj_Height = (float) (obj_Height + 13.28);
                    else if (Fixed_Degree2 > 78.26 && Fixed_Degree2 <= 80.24)
                        obj_Height = (float) (obj_Height + 14.42);
                    else if (Fixed_Degree2 > 80.24 && Fixed_Degree2 <= 82.22)
                        obj_Height = (float) (obj_Height + 15.56);
                    else if (Fixed_Degree2 > 82.22 && Fixed_Degree2 <= 84.2)
                        obj_Height = (float) (obj_Height + 16.7);
                    else if (Fixed_Degree2 > 84.2) obj_Height = (float) (obj_Height + 17.8);
                }
                else if (Distance > 250 && Distance <= 280) {
                    if (Fixed_Degree2 <= 67.5) obj_Height = (float) (obj_Height + .8);
                    else if (Fixed_Degree2 > 67.5 && Fixed_Degree2 <= 69.18)
                        obj_Height = (float) (obj_Height + 1.66);
                    else if (Fixed_Degree2 > 69.18 && Fixed_Degree2 <= 70.86)
                        obj_Height = (float) (obj_Height + 2.52);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 70.86 && Fixed_Degree2 <= 72.54)
                        obj_Height = (float) (obj_Height + 3.38);
                    else if (Fixed_Degree2 > 72.54 && Fixed_Degree2 <= 74.22)
                        obj_Height = (float) (obj_Height + 4.24);
                    else if (Fixed_Degree2 > 74.22 && Fixed_Degree2 <= 75.9)
                        obj_Height = (float) (obj_Height + 5.1);
                    else if (Fixed_Degree2 > 75.9 && Fixed_Degree2 <= 77.66)
                        obj_Height = (float) (obj_Height + 6.28); // Modified
                    else if (Fixed_Degree2 > 77.66 && Fixed_Degree2 <= 79.42)
                        obj_Height = (float) (obj_Height + 7.46);
                    else if (Fixed_Degree2 > 79.42 && Fixed_Degree2 <= 81.18)
                        obj_Height = (float) (obj_Height + 8.64);
                    else if (Fixed_Degree2 > 81.18 && Fixed_Degree2 <= 82.94)
                        obj_Height = (float) (obj_Height + 9.82);
                    else if (Fixed_Degree2 > 82.94 && Fixed_Degree2 <= 84.7)
                        obj_Height = (float) (obj_Height + 11);
                    else if (Fixed_Degree2 > 84.7) obj_Height = (float) (obj_Height + 12.2);
                }
                else if (Distance > 280 && Distance <= 310) {
                    if (Fixed_Degree2 <= 69.4) obj_Height = (float) (obj_Height + 3.1);
                    else if (Fixed_Degree2 > 69.4 && Fixed_Degree2 <= 71.04)
                        obj_Height = (float) (obj_Height + 3.9);
                    else if (Fixed_Degree2 > 71.04 && Fixed_Degree2 <= 72.68)
                        obj_Height = (float) (obj_Height + 4.7);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 72.68 && Fixed_Degree2 <= 74.32)
                        obj_Height = (float) (obj_Height + 5.5);
                    else if (Fixed_Degree2 > 74.32 && Fixed_Degree2 <= 75.96)
                        obj_Height = (float) (obj_Height + 6.3);
                    else if (Fixed_Degree2 > 75.96 && Fixed_Degree2 <= 77.6)
                        obj_Height = (float) (obj_Height + 7.1);
                    else if (Fixed_Degree2 > 77.6 && Fixed_Degree2 <= 79.16)
                        obj_Height = (float) (obj_Height + 7.8); // Modified
                    else if (Fixed_Degree2 > 79.16 && Fixed_Degree2 <= 80.72)
                        obj_Height = (float) (obj_Height + 8.5);
                    else if (Fixed_Degree2 > 80.72 && Fixed_Degree2 <= 82.28)
                        obj_Height = (float) (obj_Height + 9.2);
                    else if (Fixed_Degree2 > 82.28 && Fixed_Degree2 <= 83.84)
                        obj_Height = (float) (obj_Height + 9.9);
                    else if (Fixed_Degree2 > 83.84 && Fixed_Degree2 <= 85.4)
                        obj_Height = (float) (obj_Height + 10.6);
                    else if (Fixed_Degree2 > 85.4) obj_Height = (float) (obj_Height + 11.3);
                }
                else if (Distance > 310 && Distance <= 330) {
                    if (Fixed_Degree2 <= 70.3) obj_Height = (float) (obj_Height + 1.5);
                    else if (Fixed_Degree2 > 70.3 && Fixed_Degree2 <= 71.8)
                        obj_Height = (float) (obj_Height + 2.48);
                    else if (Fixed_Degree2 > 71.88 && Fixed_Degree2 <= 73.46)
                        obj_Height = (float) (obj_Height + 3.46);   // Modified remove if issue*************
                    else if (Fixed_Degree2 > 73.46 && Fixed_Degree2 <= 75.04)
                        obj_Height = (float) (obj_Height + 4.44);
                    else if (Fixed_Degree2 > 75.04 && Fixed_Degree2 <= 76.62)
                        obj_Height = (float) (obj_Height + 5.42);
                    else if (Fixed_Degree2 > 76.62 && Fixed_Degree2 <= 78.2)
                        obj_Height = (float) (obj_Height + 6.4);
                    else if (Fixed_Degree2 > 78.2 && Fixed_Degree2 <= 79.68)
                        obj_Height = (float) (obj_Height + 7.22); // Modified
                    else if (Fixed_Degree2 > 79.68 && Fixed_Degree2 <= 81.16)
                        obj_Height = (float) (obj_Height + 8.04);
                    else if (Fixed_Degree2 > 81.16 && Fixed_Degree2 <= 82.64)
                        obj_Height = (float) (obj_Height + 8.86);
                    else if (Fixed_Degree2 > 82.64 && Fixed_Degree2 <= 84.12)
                        obj_Height = (float) (obj_Height + 9.68);
                    else if (Fixed_Degree2 > 84.12 && Fixed_Degree2 <= 85.6)
                        obj_Height = (float) (obj_Height + 10.5);
                    else if (Fixed_Degree2 > 85.6) obj_Height = (float) (obj_Height + 11.4);
                }
            }
            Result_Height.setText(String.valueOf(obj_Height));
            elevation_Checkbox.setChecked(false);
        }
    }

}
